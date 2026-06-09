#!/usr/bin/env python3
"""Quick diagnostic for the lightweight YM flux-cancellation theorem."""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Sequence


DEFAULT_OUTPUT = Path("outputs/ym_flux_cancellation_theorem_harness.json")


@dataclass(frozen=True)
class Result:
    depth: int
    paired_faces: int
    max_flux_pair_error: float
    max_weight_mismatch: float
    max_orientation_sum: float
    promotion: bool
    checks: dict[str, bool]


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--depth", type=int, default=5)
    parser.add_argument("--quick", action="store_true")
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--json-output", type=Path, default=DEFAULT_OUTPUT)
    return parser.parse_args(argv)


def build_result(depth: int) -> Result:
    weight_mismatch = 0.0
    orientation_sum = 0.0
    flux_pair_error = 0.0
    paired = 0
    for axis in ("x", "y"):
        for idx in range(depth):
            if axis == "x":
                left, right = (0, idx), (depth - 1, idx)
                flux = 0.25 + 0.05 * idx
            else:
                left, right = (idx, 0), (idx, depth - 1)
                flux = 0.3 + 0.04 * idx
            w_left = w_right = 1.0 + idx / max(depth - 1, 1)
            s_left, s_right = -1.0, 1.0
            weight_mismatch = max(weight_mismatch, abs(w_left - w_right))
            orientation_sum = max(orientation_sum, abs(s_left + s_right))
            flux_pair_error = max(flux_pair_error, abs(w_left * s_left * flux + w_right * s_right * flux))
            paired += 1
    checks = {
        "weights_match": weight_mismatch == 0.0,
        "orientations_cancel": orientation_sum == 0.0,
        "paired_flux_sums_to_zero": flux_pair_error == 0.0,
    }
    return Result(depth, paired, flux_pair_error, weight_mismatch, orientation_sum, False, checks)


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
        print(f"paired_faces={result.paired_faces}")
        print(f"promotion={result.promotion}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
