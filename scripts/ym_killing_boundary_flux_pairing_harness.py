#!/usr/bin/env python3
"""Finite YM-1 Killing boundary flux-pairing diagnostic.

This pure-stdlib harness isolates the narrow YM-1 boundary-pairing step:

    finite periodic/opposite-face boundary carrier
    -> opposite-face involution
    -> full-degree/Killing weight preservation
    -> orientation-sign cancellation
    -> paired boundary flux cancellation on sample fields

The artifact is diagnostic only. It does not prove YM-1 finite self-adjointness,
Hamiltonian domination, OS/Wightman transfer, continuum mass gap, or Clay YM.
All promotion flags remain false.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Sequence


DEFAULT_OUTPUT = Path("outputs/ym_killing_boundary_flux_pairing_harness.json")


@dataclass(frozen=True)
class Face:
    axis: str
    side: str
    index: int
    orientation_sign: int
    weight: float
    sample_flux: float


@dataclass(frozen=True)
class FacePairSummary:
    axis: str
    pair_count: int
    max_weight_error: float
    max_orientation_sum_error: float
    max_flux_pair_error: float
    total_boundary_flux: float


@dataclass(frozen=True)
class HarnessResult:
    size: int
    quick: bool
    face_count: int
    pair_count: int
    boundary_convention: str
    opposite_face_involution_error: float
    weight_preservation_error: float
    orientation_sign_cancellation_error: float
    boundary_flux_cancellation_error: float
    left_right_total_flux: float
    bottom_top_total_flux: float
    all_boundary_flux: float
    pair_summaries: list[dict[str, Any]]
    checks: dict[str, bool]
    promotion: bool
    clay_promotion: bool
    ym_1_promotion: bool


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--size", type=int, default=6, help="Periodic side length; must be >= 2.")
    parser.add_argument("--quick", action="store_true", help="Use a smaller default size if not explicitly set.")
    parser.add_argument("--tolerance", type=float, default=1.0e-10)
    parser.add_argument("--json", action="store_true", help="Emit JSON to stdout.")
    parser.add_argument("--json-output", type=Path, default=DEFAULT_OUTPUT)
    return parser.parse_args(argv)


def validate_args(args: argparse.Namespace) -> None:
    if args.size < 2:
        raise ValueError("--size must be at least 2")
    if args.tolerance <= 0.0:
        raise ValueError("--tolerance must be positive")


def face_weight(axis: str, index: int, size: int) -> float:
    axis_offset = 0.17 if axis == "x" else 0.23
    return 1.0 + axis_offset + 0.03125 * index / max(size - 1, 1)


def face_flux_value(axis: str, index: int, size: int) -> float:
    centered = index - 0.5 * (size - 1)
    if axis == "x":
        return 0.35 + 0.11 * centered + 0.07 * ((index + 1) % 3)
    return -0.21 + 0.09 * centered - 0.05 * ((index + 2) % 4)


def build_faces(size: int) -> list[Face]:
    faces: list[Face] = []
    for index in range(size):
        x_weight = face_weight("x", index, size)
        x_flux = face_flux_value("x", index, size)
        faces.append(Face("x", "left", index, -1, x_weight, x_flux))
        faces.append(Face("x", "right", index, +1, x_weight, x_flux))

        y_weight = face_weight("y", index, size)
        y_flux = face_flux_value("y", index, size)
        faces.append(Face("y", "bottom", index, -1, y_weight, y_flux))
        faces.append(Face("y", "top", index, +1, y_weight, y_flux))
    return faces


def opposite_side(side: str) -> str:
    return {
        "left": "right",
        "right": "left",
        "bottom": "top",
        "top": "bottom",
    }[side]


def face_lookup(faces: Sequence[Face]) -> dict[tuple[str, str, int], Face]:
    return {(face.axis, face.side, face.index): face for face in faces}


def pair_flux(face: Face) -> float:
    return face.orientation_sign * face.weight * face.sample_flux


def build_pair_summaries(faces: Sequence[Face], tolerance: float) -> tuple[list[FacePairSummary], dict[str, bool], dict[str, float]]:
    lookup = face_lookup(faces)
    visited: set[tuple[str, str, int]] = set()
    summaries: list[FacePairSummary] = []
    max_involution_error = 0.0
    max_weight_error = 0.0
    max_sign_error = 0.0
    max_flux_error = 0.0
    totals = {"x": 0.0, "y": 0.0}

    for axis in ("x", "y"):
        pair_count = 0
        axis_max_weight = 0.0
        axis_max_sign = 0.0
        axis_max_flux = 0.0
        axis_total = 0.0
        sides = ("left", "right") if axis == "x" else ("bottom", "top")
        for side in sides:
            for index in range(len(faces) // 4):
                key = (axis, side, index)
                if key in visited or key not in lookup:
                    continue
                face = lookup[key]
                opposite = lookup[(axis, opposite_side(side), index)]
                visited.add(key)
                visited.add((opposite.axis, opposite.side, opposite.index))

                involution = lookup[(opposite.axis, opposite_side(opposite.side), opposite.index)]
                involution_error = 0.0 if involution == face else 1.0
                max_involution_error = max(max_involution_error, involution_error)

                weight_error = abs(face.weight - opposite.weight)
                sign_error = abs(face.orientation_sign + opposite.orientation_sign)
                flux_error = abs(pair_flux(face) + pair_flux(opposite))

                axis_max_weight = max(axis_max_weight, weight_error)
                axis_max_sign = max(axis_max_sign, sign_error)
                axis_max_flux = max(axis_max_flux, flux_error)
                max_weight_error = max(max_weight_error, weight_error)
                max_sign_error = max(max_sign_error, sign_error)
                max_flux_error = max(max_flux_error, flux_error)

                axis_total += pair_flux(face) + pair_flux(opposite)
                pair_count += 1

        totals[axis] = axis_total
        summaries.append(
            FacePairSummary(
                axis=axis,
                pair_count=pair_count,
                max_weight_error=axis_max_weight,
                max_orientation_sum_error=axis_max_sign,
                max_flux_pair_error=axis_max_flux,
                total_boundary_flux=axis_total,
            )
        )

    checks = {
        "opposite_face_involution": max_involution_error <= tolerance,
        "weight_preservation": max_weight_error <= tolerance,
        "orientation_sign_cancellation": max_sign_error <= tolerance,
        "boundary_flux_cancellation": max_flux_error <= tolerance and abs(totals["x"] + totals["y"]) <= tolerance,
    }
    metrics = {
        "opposite_face_involution_error": max_involution_error,
        "weight_preservation_error": max_weight_error,
        "orientation_sign_cancellation_error": max_sign_error,
        "boundary_flux_cancellation_error": max_flux_error,
        "left_right_total_flux": totals["x"],
        "bottom_top_total_flux": totals["y"],
        "all_boundary_flux": totals["x"] + totals["y"],
    }
    return summaries, checks, metrics


def run(size: int, quick: bool, tolerance: float) -> HarnessResult:
    effective_size = min(size, 4) if quick else size
    faces = build_faces(effective_size)
    pair_summaries, checks, metrics = build_pair_summaries(faces, tolerance)

    return HarnessResult(
        size=effective_size,
        quick=quick,
        face_count=len(faces),
        pair_count=sum(summary.pair_count for summary in pair_summaries),
        boundary_convention="periodic_opposite_face_killing_full_degree_pairing",
        opposite_face_involution_error=metrics["opposite_face_involution_error"],
        weight_preservation_error=metrics["weight_preservation_error"],
        orientation_sign_cancellation_error=metrics["orientation_sign_cancellation_error"],
        boundary_flux_cancellation_error=metrics["boundary_flux_cancellation_error"],
        left_right_total_flux=metrics["left_right_total_flux"],
        bottom_top_total_flux=metrics["bottom_top_total_flux"],
        all_boundary_flux=metrics["all_boundary_flux"],
        pair_summaries=[asdict(summary) for summary in pair_summaries],
        checks=checks,
        promotion=False,
        clay_promotion=False,
        ym_1_promotion=False,
    )


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    validate_args(args)
    result = run(args.size, args.quick, args.tolerance)

    payload: dict[str, Any] = {
        "control": {
            "O": "Single-file finite YM boundary-pairing diagnostic.",
            "R": "Isolate opposite-face involution, weight preservation, orientation cancellation, and boundary flux cancellation for YM-1.",
            "C": "scripts/ym_killing_boundary_flux_pairing_harness.py",
            "S": "Finite periodic/opposite-face carrier only; no theorem authority.",
            "L": "build boundary faces -> pair faces -> check weights/signs/flux -> fail-closed JSON",
            "P": "Use a narrow diagnostic instead of the broader self-adjointness harness when the target is the YM-1 boundary pairing step.",
            "G": "Promotion flags remain false; no YM-1 theorem, no Clay YM, no terminal authority.",
            "F": "Does not prove finite Hodge adjointness, quotient self-adjointness, Hamiltonian domination, OS/Wightman transfer, or continuum mass gap.",
        },
        "result": asdict(result),
        "ok": all(result.checks.values()),
        "not_proved": [
            "YM-1 finite theorem",
            "finite Hodge adjointness",
            "quotient self-adjoint Hamiltonian",
            "Hamiltonian domination",
            "OS/Wightman reconstruction",
            "continuum mass gap",
            "Clay Yang-Mills",
        ],
    }

    args.json_output.parent.mkdir(parents=True, exist_ok=True)
    args.json_output.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    if args.json:
        print(json.dumps(payload, sort_keys=True))
    else:
        print(f"wrote {args.json_output}")
        print(
            "involution_error={:.3e} weight_error={:.3e} sign_error={:.3e} flux_error={:.3e}".format(
                result.opposite_face_involution_error,
                result.weight_preservation_error,
                result.orientation_sign_cancellation_error,
                result.boundary_flux_cancellation_error,
            )
        )
        print("promotion=false")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
