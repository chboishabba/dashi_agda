#!/usr/bin/env python3
"""Quick diagnostic for the lightweight YM opposite-face involution theorem."""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Sequence


DEFAULT_OUTPUT = Path("outputs/ym_opposite_face_involution_theorem_harness.json")


@dataclass(frozen=True)
class Result:
    depth: int
    max_roundtrip_error: int
    max_orientation_cancel_error: float
    max_axis_preservation_error: int
    max_weight_error: float
    promotion: bool
    checks: dict[str, bool]


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--depth", type=int, default=5)
    parser.add_argument("--quick", action="store_true")
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--json-output", type=Path, default=DEFAULT_OUTPUT)
    return parser.parse_args(argv)


def opposite(face: tuple[int, int], axis: str, depth: int) -> tuple[int, int]:
    x, y = face
    return (depth - 1 - x, y) if axis == "x" else (x, depth - 1 - y)


def orientation(face: tuple[int, int], axis: str) -> float:
    x, y = face
    return -1.0 if ((axis == "x" and x == 0) or (axis == "y" and y == 0)) else 1.0


def weight(face: tuple[int, int], axis: str, depth: int) -> float:
    x, y = face
    mirrored = y if axis == "x" else x
    return 1.0 + mirrored / max(depth - 1, 1)


def build_result(depth: int) -> Result:
    roundtrip = 0
    orientation_error = 0.0
    axis_error = 0
    weight_error = 0.0
    for axis in ("x", "y"):
        boundary = [(0, j) for j in range(depth)] if axis == "x" else [(i, 0) for i in range(depth)]
        for face in boundary:
            other = opposite(face, axis, depth)
            back = opposite(other, axis, depth)
            roundtrip = max(roundtrip, abs(back[0] - face[0]) + abs(back[1] - face[1]))
            orientation_error = max(orientation_error, abs(orientation(face, axis) + orientation(other, axis)))
            if axis == "x":
                axis_error = max(axis_error, abs(face[1] - other[1]))
            else:
                axis_error = max(axis_error, abs(face[0] - other[0]))
            weight_error = max(weight_error, abs(weight(face, axis, depth) - weight(other, axis, depth)))
    checks = {
        "roundtrip_involution": roundtrip == 0,
        "orientation_cancels": orientation_error == 0.0,
        "axis_preserved": axis_error == 0,
        "weights_match": weight_error == 0.0,
    }
    return Result(depth, roundtrip, orientation_error, axis_error, weight_error, False, checks)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    depth = 3 if args.quick else args.depth
    result = build_result(depth)
    payload = asdict(result)
    args.json_output.parent.mkdir(parents=True, exist_ok=True)
    args.json_output.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    if args.json:
        print(json.dumps(payload, indent=2, sort_keys=True))
    else:
        print(f"max_roundtrip_error={result.max_roundtrip_error}")
        print(f"promotion={result.promotion}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
