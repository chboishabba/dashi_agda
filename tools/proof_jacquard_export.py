#!/usr/bin/env python3
"""Export proof-carrying Jacquard tape to loom-ready lift rasters.

Input is a JSON document containing self-describing proof frames.  The exporter:

1. validates local parity and the frame grammar before emitting loom data;
2. packs certificate metadata into reserved physical warp-end lanes;
3. emits the exact per-pick/per-end lift raster as JSON and 24-bit BMP;
4. optionally emits WIF 1.1 liftplan mode *only* when a supplied shaft
   assignment is proven compatible with every row.

The bitmap backend is intended for image-driven individual-thread Jacquard
controllers.  Vendor-specific formats such as J1P are deliberately not guessed.
Machine orientation is explicit in the profile (reverse picks/ends, invert).
"""

from __future__ import annotations

import argparse
import json
import struct
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable, Sequence

SYNC = [1, 0, 1, 0]
KIND_CODE = {
    "start": 0,
    "motif_begin": 1,
    "continuation": 2,
    "provenance": 3,
    "motif_end": 4,
    "stop": 5,
}
MOTIF_CODE = {
    "premise": 0,
    "branch": 1,
    "discharge": 2,
    "rewrite": 3,
    "lemma_reference": 4,
    "conclusion": 5,
}


@dataclass(frozen=True)
class Layout:
    step_bits: int = 16
    continuation_bits: int = 8
    provenance_bits: int = 16


@dataclass(frozen=True)
class MachineProfile:
    reverse_picks: bool = False
    reverse_ends: bool = False
    invert: bool = False


def parity(bits: Iterable[int]) -> int:
    p = 0
    for bit in bits:
        if bit not in (0, 1):
            raise ValueError(f"non-bit value {bit!r}")
        p ^= bit
    return p


def int_bits(value: int, width: int) -> list[int]:
    if value < 0 or value >= (1 << width):
        raise ValueError(f"value {value} does not fit in {width} bits")
    return [(value >> shift) & 1 for shift in reversed(range(width))]


def code_bits(value: int, width: int) -> list[int]:
    return int_bits(value, width)


def bool_bit(value: Any) -> int:
    if value is True or value == 1:
        return 1
    if value is False or value == 0:
        return 0
    raise ValueError(f"expected Boolean/bit, got {value!r}")


def payload_bits(frame: dict[str, Any], payload_width: int) -> list[int]:
    raw = frame.get("payload_bits", [0] * payload_width)
    bits = [bool_bit(x) for x in raw]
    if len(bits) != payload_width:
        raise ValueError(
            f"payload width {len(bits)} does not match declared {payload_width}"
        )
    return bits


def metadata_without_parity(
    frame: dict[str, Any], layout: Layout, payload_width: int
) -> list[int]:
    kind = frame["kind"]
    motif = frame.get("motif", "premise")
    if kind not in KIND_CODE:
        raise ValueError(f"unknown frame kind {kind!r}")
    if motif not in MOTIF_CODE:
        raise ValueError(f"unknown motif {motif!r}")
    step = int(frame.get("proof_step_id", 0))
    cont = int(frame.get("continuation_id", 0))
    prov = int(frame.get("provenance_id", 0))
    return (
        SYNC
        + code_bits(KIND_CODE[kind], 3)
        + int_bits(step, layout.step_bits)
        + int_bits(cont, layout.continuation_bits)
        + code_bits(MOTIF_CODE[motif], 3)
        + int_bits(prov, layout.provenance_bits)
        + payload_bits(frame, payload_width)
    )


def expected_parity(frame: dict[str, Any], layout: Layout, payload_width: int) -> int:
    # The parity covers every physical lane except the parity lane itself,
    # including the sync marker.  A one-bit corruption in the complete row is
    # therefore detected by the local check.
    return parity(metadata_without_parity(frame, layout, payload_width))


def physical_row(frame: dict[str, Any], layout: Layout, payload_width: int) -> list[int]:
    body = metadata_without_parity(frame, layout, payload_width)
    p = bool_bit(frame.get("parity_bit", expected_parity(frame, layout, payload_width)))
    return body + [p]


def validate_local(frame: dict[str, Any], layout: Layout, payload_width: int) -> None:
    supplied = bool_bit(frame.get("parity_bit", expected_parity(frame, layout, payload_width)))
    expected = expected_parity(frame, layout, payload_width)
    if supplied != expected:
        raise ValueError(
            f"local parity failure at proof step {frame.get('proof_step_id', 0)}: "
            f"supplied {supplied}, expected {expected}"
        )


def validate_structure(frames: Sequence[dict[str, Any]]) -> None:
    phase = "expect_start"
    active_step: int | None = None
    next_cont = 0

    for index, frame in enumerate(frames):
        kind = frame["kind"]
        step = int(frame.get("proof_step_id", 0))
        cont = int(frame.get("continuation_id", 0))

        if phase == "expect_start":
            if kind != "start":
                raise ValueError(f"frame {index}: expected start, got {kind}")
            phase = "between"
        elif phase == "between":
            if kind == "motif_begin":
                active_step = step
                phase = "expect_provenance"
            elif kind == "stop":
                phase = "finished"
            else:
                raise ValueError(f"frame {index}: expected motif_begin/stop, got {kind}")
        elif phase == "expect_provenance":
            if kind != "provenance" or step != active_step:
                raise ValueError(f"frame {index}: invalid provenance frame")
            next_cont = 0
            phase = "expect_continuation"
        elif phase == "expect_continuation":
            if kind != "continuation" or step != active_step or cont != next_cont:
                raise ValueError(
                    f"frame {index}: expected continuation {next_cont} for step {active_step}"
                )
            if bool(frame.get("more", False)):
                next_cont += 1
            else:
                phase = "expect_motif_end"
        elif phase == "expect_motif_end":
            if kind != "motif_end" or step != active_step:
                raise ValueError(f"frame {index}: invalid motif_end")
            active_step = None
            phase = "between"
        elif phase == "finished":
            raise ValueError(f"frame {index}: data occurs after stop frame")

    if phase != "finished":
        raise ValueError(f"tape ended in incomplete phase {phase}")


def orient_rows(rows: Sequence[Sequence[int]], profile: MachineProfile) -> list[list[int]]:
    out = [list(row) for row in rows]
    if profile.reverse_ends:
        out = [list(reversed(row)) for row in out]
    if profile.invert:
        out = [[1 - b for b in row] for row in out]
    if profile.reverse_picks:
        out.reverse()
    return out


def write_bmp(path: Path, rows: Sequence[Sequence[int]]) -> None:
    if not rows:
        raise ValueError("cannot write empty raster")
    width = len(rows[0])
    height = len(rows)
    if width == 0 or any(len(row) != width for row in rows):
        raise ValueError("raster must be non-empty and rectangular")

    # 24-bit BI_RGB is deliberately simple and broadly importable.
    row_bytes = width * 3
    stride = (row_bytes + 3) & ~3
    pixel_bytes = stride * height
    offset = 14 + 40
    file_size = offset + pixel_bytes

    with path.open("wb") as f:
        f.write(struct.pack("<2sIHHI", b"BM", file_size, 0, 0, offset))
        f.write(
            struct.pack(
                "<IIIHHIIIIII",
                40,
                width,
                height,
                1,
                24,
                0,
                pixel_bytes,
                2835,
                2835,
                0,
                0,
            )
        )
        # Positive BMP height is bottom-up. Reverse here so input row 0 appears
        # visually at the top; machine pick orientation remains profile-owned.
        pad = b"\x00" * (stride - row_bytes)
        for row in reversed(rows):
            for bit in row:
                v = 0 if bit else 255
                f.write(bytes((v, v, v)))
            f.write(pad)


def verify_shaft_factorisation(
    rows: Sequence[Sequence[int]], shaft_assignment: Sequence[int]
) -> tuple[int, list[list[int]]]:
    if not rows:
        raise ValueError("empty raster")
    width = len(rows[0])
    if len(shaft_assignment) != width:
        raise ValueError("shaft_assignment length must equal raster width")
    if any(s <= 0 for s in shaft_assignment):
        raise ValueError("WIF shaft numbers are 1-based positive integers")
    shafts = max(shaft_assignment)
    liftplan: list[list[int]] = []
    for pick, row in enumerate(rows, 1):
        shaft_values: dict[int, int] = {}
        for end, (shaft, bit) in enumerate(zip(shaft_assignment, row), 1):
            previous = shaft_values.setdefault(shaft, bit)
            if previous != bit:
                raise ValueError(
                    f"row {pick}: ends sharing shaft {shaft} disagree "
                    f"(including end {end}); raster is not shaft-factorable"
                )
        liftplan.append(sorted(s for s, bit in shaft_values.items() if bit))
    return shafts, liftplan


def write_wif(
    path: Path,
    rows: Sequence[Sequence[int]],
    shaft_assignment: Sequence[int],
) -> None:
    shafts, liftplan = verify_shaft_factorisation(rows, shaft_assignment)
    width = len(rows[0])
    lines = [
        "[WIF]",
        "Version=1.1",
        "Date=April 20, 1997",
        "Developers=DASHI proof-carrying textile compiler",
        "Source Program=DASHI proof_jacquard_export.py",
        "Source Version=0.1",
        "",
        "[CONTENTS]",
        "WEAVING=true",
        "WARP=true",
        "WEFT=true",
        "THREADING=true",
        "LIFTPLAN=true",
        "",
        "[WEAVING]",
        f"Shafts={shafts}",
        "Treadles=0",
        "Rising Shed=true",
        "",
        "[WARP]",
        f"Threads={width}",
        "",
        "[WEFT]",
        f"Threads={len(rows)}",
        "",
        "[THREADING]",
    ]
    lines.extend(f"{i}={shaft}" for i, shaft in enumerate(shaft_assignment, 1))
    lines.extend(["", "[LIFTPLAN]"])
    for pick, raised in enumerate(liftplan, 1):
        lines.append(f"{pick}=" + ",".join(map(str, raised)))
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def load_document(path: Path) -> tuple[Layout, MachineProfile, int, list[dict[str, Any]], Any]:
    doc = json.loads(path.read_text(encoding="utf-8"))
    payload_width = int(doc["payload_width"])
    l = doc.get("layout", {})
    layout = Layout(
        step_bits=int(l.get("step_bits", 16)),
        continuation_bits=int(l.get("continuation_bits", 8)),
        provenance_bits=int(l.get("provenance_bits", 16)),
    )
    p = doc.get("machine_profile", {})
    profile = MachineProfile(
        reverse_picks=bool(p.get("reverse_picks", False)),
        reverse_ends=bool(p.get("reverse_ends", False)),
        invert=bool(p.get("invert", False)),
    )
    frames = doc["frames"]
    if not isinstance(frames, list):
        raise ValueError("frames must be a list")
    return layout, profile, payload_width, frames, doc.get("shaft_assignment")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("--out-prefix", type=Path, required=True)
    parser.add_argument("--wif", action="store_true", help="also emit WIF if shaft-factorable")
    args = parser.parse_args()

    layout, profile, payload_width, frames, shaft_assignment = load_document(args.input)
    for frame in frames:
        validate_local(frame, layout, payload_width)
    validate_structure(frames)

    rows = [physical_row(frame, layout, payload_width) for frame in frames]
    rows = orient_rows(rows, profile)

    prefix = args.out_prefix
    prefix.parent.mkdir(parents=True, exist_ok=True)
    raster_path = prefix.with_suffix(".liftplan.json")
    bmp_path = prefix.with_suffix(".bmp")
    raster_path.write_text(
        json.dumps(
            {
                "width": len(rows[0]) if rows else 0,
                "picks": len(rows),
                "rows": rows,
                "machine_profile": profile.__dict__,
            },
            indent=2,
        )
        + "\n",
        encoding="utf-8",
    )
    write_bmp(bmp_path, rows)

    if args.wif:
        if shaft_assignment is None:
            raise ValueError("--wif requires shaft_assignment in input JSON")
        write_wif(prefix.with_suffix(".wif"), rows, [int(x) for x in shaft_assignment])

    print(f"validated {len(frames)} frames")
    print(f"loom raster: {len(rows)} picks x {len(rows[0]) if rows else 0} ends")
    print(raster_path)
    print(bmp_path)
    if args.wif:
        print(prefix.with_suffix(".wif"))


if __name__ == "__main__":
    main()
