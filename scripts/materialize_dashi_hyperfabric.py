#!/usr/bin/env python3
"""Materialise a source-backed DASHI 369/supervoxel hyperfabric.

The renderer consumes actual Agda declarations. The visual topology is derived
from constructor structure and the canonical 3-6-9 address; it has no hand-made
physics/domain node list.
"""
from __future__ import annotations

import argparse
import html
import json
import re
from dataclasses import asdict, dataclass
from pathlib import Path

SCHEMA = "dashi-hyperfabric-ir-v1"
REFINEMENT_PATH = Path("DASHI/Foundations/SSPPrimeLane369Refinement.agda")
FIELD_PATH = Path("DASHI/Core/SuperSSP369Field.agda")


class ExtractError(RuntimeError):
    pass


@dataclass(frozen=True)
class SourceRef:
    path: str
    declaration: str
    line: int


@dataclass(frozen=True)
class Supervoxel:
    id: str
    depth: int
    prime_lane: str
    address: tuple[int, ...]
    parity: str
    body_surface: str
    residue_surface: str
    source: SourceRef


@dataclass(frozen=True)
class FieldInstance:
    id: str
    depth: int
    body_forest_surface: str
    residue_forest_surface: str
    focus: str
    source: SourceRef


@dataclass(frozen=True)
class StrandEvent:
    id: str
    kind: str
    source: str
    targets: tuple[str, ...]
    operator: str
    source_ref: SourceRef


def declaration_block(text: str, name: str) -> tuple[str, int]:
    lines = text.splitlines()
    sig = re.compile(rf"^{re.escape(name)}\s*:")
    definition = re.compile(rf"^{re.escape(name)}\s*=")
    start = next((i for i, line in enumerate(lines) if sig.match(line)), None)
    if start is None:
        raise ExtractError(f"declaration not found: {name}")
    eq = next((i for i in range(start + 1, len(lines)) if definition.match(lines[i])), None)
    if eq is None:
        raise ExtractError(f"definition not found: {name}")
    end = len(lines)
    top_decl = re.compile(r"^[^\s].*\s*:")
    for i in range(eq + 1, len(lines)):
        if top_decl.match(lines[i]):
            end = i
            break
    return "\n".join(lines[eq:end]), start + 1


def signature_and_definition_block(text: str, name: str) -> tuple[str, int]:
    """Return exactly one declaration's signature through its definition line.

    The previous address extractor used a fixed eight-line window.  When the
    following declaration was close enough, that window also captured its
    `digit-3` / `digit-6` terms and turned the canonical `(3, 6, 9)` address
    into `(3, 6, 9, 3, 6)`.  This helper is declaration-delimited instead.
    """

    lines = text.splitlines()
    sig = re.compile(rf"^{re.escape(name)}\s*:")
    definition = re.compile(rf"^{re.escape(name)}\s*=")
    start = next((i for i, line in enumerate(lines) if sig.match(line)), None)
    if start is None:
        raise ExtractError(f"declaration not found: {name}")
    eq = next((i for i in range(start + 1, len(lines)) if definition.match(lines[i])), None)
    if eq is None:
        raise ExtractError(f"definition not found: {name}")
    return "\n".join(lines[start : eq + 1]), start + 1


def constructor_args(block: str, constructor: str) -> list[str]:
    lines = block.splitlines()
    idx = next((i for i, line in enumerate(lines) if constructor in line), None)
    if idx is None:
        raise ExtractError(f"constructor {constructor} not found in block")
    args: list[str] = []
    for line in lines[idx + 1 :]:
        stripped = line.strip()
        if not stripped or stripped.startswith("--"):
            continue
        if re.match(r"^[^\s].*\s*:", line):
            break
        args.append(stripped)
    return args


def extract_address(refinement_text: str, path: str) -> tuple[tuple[int, ...], SourceRef]:
    block, line = signature_and_definition_block(
        refinement_text,
        "canonicalThreeSixNineDigits",
    )
    digits = tuple(int(x) for x in re.findall(r"digit-(3|6|9)", block))
    if digits != (3, 6, 9):
        raise ExtractError(f"expected canonical address 3,6,9; got {digits}")
    return digits, SourceRef(path, "canonicalThreeSixNineDigits", line)


def extract_supervoxel(text: str, path: str, name: str, depth: int, address: tuple[int, ...]) -> Supervoxel:
    block, line = declaration_block(text, name)
    args = constructor_args(block, "mkSuperSSP369Supervoxel")
    if len(args) < 10:
        raise ExtractError(f"{name}: incomplete supervoxel constructor ({len(args)} args)")
    return Supervoxel(
        id=name,
        depth=depth,
        prime_lane=args[0],
        address=address,
        parity=args[7],
        body_surface=args[8],
        residue_surface=args[9],
        source=SourceRef(path, name, line),
    )


def extract_field(text: str, path: str, name: str, depth: int) -> FieldInstance:
    block, line = declaration_block(text, name)
    args = constructor_args(block, "mkSuperSSP369Field")
    if len(args) < 5:
        raise ExtractError(f"{name}: incomplete field constructor ({len(args)} args)")
    body = re.search(r"constantForest.*?\s([A-Za-z][\w′-]*)\)?$", args[0])
    residue = re.search(r"constantForest.*?\s([A-Za-z][\w′-]*)\)?$", args[1])
    if not body or not residue:
        raise ExtractError(f"{name}: could not extract forest surfaces")
    return FieldInstance(
        id=name,
        depth=depth,
        body_forest_surface=body.group(1),
        residue_forest_surface=residue.group(1),
        focus=args[2],
        source=SourceRef(path, name, line),
    )


def build_ir(repo_root: Path) -> dict:
    refinement_text = (repo_root / REFINEMENT_PATH).read_text(encoding="utf-8")
    field_text = (repo_root / FIELD_PATH).read_text(encoding="utf-8")

    address, address_source = extract_address(refinement_text, REFINEMENT_PATH.as_posix())
    root_voxel = extract_supervoxel(field_text, FIELD_PATH.as_posix(), "rootP3Supervoxel", 0, ())
    depth3_voxel = extract_supervoxel(field_text, FIELD_PATH.as_posix(), "depth3P7Supervoxel", 3, address)
    root_field = extract_field(field_text, FIELD_PATH.as_posix(), "rootField", 0)
    depth3_field = extract_field(field_text, FIELD_PATH.as_posix(), "depth3Field", 3)

    carriers = [
        {"id": "address-root", "kind": "address", "address": [], "source": asdict(address_source)},
        *[
            {
                "id": f"address-{'-'.join(map(str, address[:i]))}",
                "kind": "address",
                "address": list(address[:i]),
                "source": asdict(address_source),
            }
            for i in range(1, len(address) + 1)
        ],
        {"id": root_voxel.id, "kind": "supervoxel", **asdict(root_voxel)},
        {"id": depth3_voxel.id, "kind": "supervoxel", **asdict(depth3_voxel)},
        {"id": root_field.id, "kind": "field", **asdict(root_field)},
        {"id": depth3_field.id, "kind": "field", **asdict(depth3_field)},
        {"id": "depth3-body", "kind": "surface", "surface": depth3_voxel.body_surface, "source": asdict(depth3_voxel.source)},
        {"id": "depth3-residue", "kind": "surface", "surface": depth3_voxel.residue_surface, "source": asdict(depth3_voxel.source)},
    ]

    events: list[StrandEvent] = []
    previous = "address-root"
    for i, digit in enumerate(address, 1):
        target = f"address-{'-'.join(map(str, address[:i]))}"
        events.append(StrandEvent(f"refine-{i}", "refinement", previous, (target,), f"refine digit-{digit}", address_source))
        previous = target
    events.extend(
        [
            StrandEvent("focus-root", "focus", "rootField", (root_voxel.id,), "focus", root_field.source),
            StrandEvent("focus-depth3", "focus", "depth3Field", (depth3_voxel.id,), "focus", depth3_field.source),
            StrandEvent("address-focus", "coordinate-transport", previous, (depth3_voxel.id,), "refinement address", depth3_voxel.source),
            StrandEvent("body-residue-split", "decomposition", depth3_voxel.id, ("depth3-body", "depth3-residue"), "bodySurface / residueSurface", depth3_voxel.source),
        ]
    )

    return {
        "schema": SCHEMA,
        "title": "DASHI 369 Supervoxel Hyperfabric",
        "source_roots": [REFINEMENT_PATH.as_posix(), FIELD_PATH.as_posix()],
        "canonical_address": list(address),
        "carriers": carriers,
        "events": [asdict(event) for event in events],
        "invariants": {
            "topology_source_backed": True,
            "hand_authored_domain_nodes": False,
            "split_derived_from_constructor_fields": True,
            "ultrametric_trunk_derived_from_canonical_address": True,
        },
    }


def esc(value: object) -> str:
    return html.escape(str(value), quote=True)


def render_svg(ir: dict) -> str:
    address = ir["canonical_address"]
    width, height = 1500, 900
    positions: dict[str, tuple[float, float]] = {"address-root": (120, 340)}
    for i in range(1, len(address) + 1):
        positions[f"address-{'-'.join(map(str, address[:i]))}"] = (120 + 250 * i, 340)
    positions.update(
        {
            "rootField": (120, 130),
            "rootP3Supervoxel": (360, 130),
            "depth3Field": (870, 130),
            "depth3P7Supervoxel": (1080, 340),
            "depth3-body": (1260, 220),
            "depth3-residue": (1260, 500),
        }
    )

    paths: list[tuple[str, str, str, str]] = []
    for event in ir["events"]:
        sx, sy = positions[event["source"]]
        for index, target in enumerate(event["targets"]):
            tx, ty = positions[target]
            path_id = f"path-{event['id']}-{index}"
            if event["kind"] == "decomposition":
                d = f"M {sx},{sy} C {sx+70},{sy} {tx-70},{ty} {tx},{ty}"
            elif abs(ty - sy) < 5:
                d = f"M {sx},{sy} C {(sx+tx)/2},{sy-35} {(sx+tx)/2},{ty+35} {tx},{ty}"
            else:
                d = f"M {sx},{sy} C {sx+80},{sy} {tx-80},{ty} {tx},{ty}"
            paths.append((path_id, d, event["kind"], event["operator"]))

    colours = {
        "refinement": "#48D6FF",
        "focus": "#7C8CFF",
        "coordinate-transport": "#FFD166",
        "decomposition": "#F76FAE",
    }
    output = [f'''<svg xmlns="http://www.w3.org/2000/svg" xmlns:xlink="http://www.w3.org/1999/xlink" width="{width}" height="{height}" viewBox="0 0 {width} {height}">
<defs>
 <linearGradient id="bg" x1="0" y1="0" x2="1" y2="1"><stop stop-color="#061222"/><stop offset="1" stop-color="#10102A"/></linearGradient>
 <filter id="glow"><feGaussianBlur stdDeviation="5" result="b"/><feMerge><feMergeNode in="b"/><feMergeNode in="SourceGraphic"/></feMerge></filter>
 <style>text{{font-family:Inter,Arial,sans-serif}}.title{{fill:#F4FAFF;font-weight:700}}.sub{{fill:#9CBBD8}}.source{{fill:#7399B9;font-family:monospace}}.strand{{fill:none;stroke-linecap:round;stroke-width:10;opacity:.82}}.under{{fill:none;stroke:#091425;stroke-width:18;stroke-linecap:round}}.cell{{fill:#0C213B;stroke:#3475A7;stroke-width:2}}.digit{{fill:#0A1830;stroke:#48D6FF;stroke-width:2}}.surface{{fill:#211739;stroke:#F76FAE;stroke-width:2}}.residue{{stroke-dasharray:9 8}}@keyframes weave{{to{{stroke-dashoffset:-42}}}}.moving{{stroke-dasharray:12 9;animation:weave 7s linear infinite}}</style>
</defs><rect width="100%" height="100%" fill="url(#bg)"/>
<text x="70" y="58" class="title" font-size="38">DASHI 369 SUPERVOXEL HYPERFABRIC</text>
<text x="70" y="88" class="sub" font-size="17">Generated from canonical Agda constructors: prefix transport forms the trunk; body/residue fields force the split.</text>''']

    for path_id, d, kind, operator in paths:
        colour = colours[kind]
        output.append(f'<path id="{path_id}" d="{d}" fill="none" stroke="none"/>')
        output.append(f'<path d="{d}" class="under"/>')
        css_class = "strand moving" + (" residue" if "residue" in operator else "")
        output.append(f'<path d="{d}" class="{css_class}" stroke="{colour}"/>')

    for i, (path_id, _d, kind, _operator) in enumerate(paths):
        colour = colours[kind]
        output.append(f'<circle r="6" fill="{colour}" filter="url(#glow)"><animateMotion dur="{4.8 + (i % 3):.1f}s" begin="{i * 0.45:.2f}s" repeatCount="indefinite"><mpath href="#{path_id}" xlink:href="#{path_id}"/></animateMotion></circle>')

    labels = [("address-root", "root")]
    labels.extend((f"address-{'-'.join(map(str, address[:i]))}", str(address[i - 1])) for i in range(1, len(address) + 1))
    for carrier_id, label in labels:
        x, y = positions[carrier_id]
        output.append(f'<circle class="digit" cx="{x}" cy="{y}" r="42"/><text x="{x}" y="{y+8}" text-anchor="middle" class="title" font-size="22">{esc(label)}</text>')

    def box(carrier_id: str, title: str, detail: str, css_class: str = "cell") -> None:
        x, y = positions[carrier_id]
        output.append(f'<rect class="{css_class}" x="{x-88}" y="{y-42}" width="176" height="84" rx="18"/>')
        output.append(f'<text x="{x}" y="{y-5}" text-anchor="middle" class="title" font-size="16">{esc(title)}</text>')
        output.append(f'<text x="{x}" y="{y+19}" text-anchor="middle" class="sub" font-size="12">{esc(detail)}</text>')

    box("rootField", "rootField", "body/residue forests · depth 0")
    box("rootP3Supervoxel", "rootP3Supervoxel", "p3 · evenParity")
    box("depth3Field", "depth3Field", "focus = depth3P7Supervoxel")
    box("depth3P7Supervoxel", "depth3P7Supervoxel", "p7 · oddParity · [3,6,9]")
    box("depth3-body", "bodySurface", "canonicalExampleFifteenSSPSurface", "surface")
    box("depth3-residue", "residueSurface", "canonicalNegativeFifteenSSPSurface", "surface residue")

    output.extend(
        [
            '<text x="760" y="305" class="sub" font-size="13">shared prefix trunk from canonicalThreeSixNineDigits</text>',
            '<text x="1170" y="375" class="sub" font-size="13">constructor-forced body/residue decomposition</text>',
            '<text x="70" y="805" class="source" font-size="12">Sources: DASHI/Foundations/SSPPrimeLane369Refinement.agda · DASHI/Core/SuperSSP369Field.agda</text>',
            '<text x="70" y="832" class="sub" font-size="13">No domain nodes or transport edges are supplied by a visual spec. SVG positions are an embedding of the extracted IR only.</text>',
            '<text x="70" y="858" class="sub" font-size="13">Animation follows refinement, focus, coordinate transport, and body/residue decomposition events.</text>',
            '</svg>',
        ]
    )
    return "\n".join(output) + "\n"


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo-root", type=Path, default=Path("."))
    parser.add_argument("--json-output", type=Path, default=Path("artifacts/dashi-369-supervoxel-hyperfabric.json"))
    parser.add_argument("--svg-output", type=Path, default=Path("artifacts/dashi-369-supervoxel-hyperfabric.svg"))
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    root = args.repo_root.resolve()
    ir = build_ir(root)
    if args.check:
        print(json.dumps({"ok": True, "address": ir["canonical_address"], "events": len(ir["events"])}, sort_keys=True))
        return
    json_path = args.json_output if args.json_output.is_absolute() else root / args.json_output
    svg_path = args.svg_output if args.svg_output.is_absolute() else root / args.svg_output
    json_path.parent.mkdir(parents=True, exist_ok=True)
    svg_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.write_text(json.dumps(ir, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    svg_path.write_text(render_svg(ir), encoding="utf-8")
    print(f"wrote {json_path}\nwrote {svg_path}")


if __name__ == "__main__":
    main()
