#!/usr/bin/env python3
"""Quick diagnostic for the lightweight YM quotient-symmetry theorem."""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Sequence


DEFAULT_OUTPUT = Path("outputs/ym_quotient_symmetry_theorem_harness.json")


@dataclass(frozen=True)
class Result:
    matrix_symmetry_error: float
    rayleigh_min: float
    null_mode_error: float
    promotion: bool
    checks: dict[str, bool]


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--quick", action="store_true")
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--json-output", type=Path, default=DEFAULT_OUTPUT)
    return parser.parse_args(argv)


def build_result() -> Result:
    matrix = (
        (2.0, -1.0, -1.0),
        (-1.0, 2.0, -1.0),
        (-1.0, -1.0, 2.0),
    )
    symmetry_error = max(abs(matrix[i][j] - matrix[j][i]) for i in range(3) for j in range(3))
    vecs = ((1.0, -1.0, 0.0), (1.0, 0.0, -1.0), (0.0, 1.0, -1.0))
    rayleighs = []
    for v in vecs:
        mv = [sum(matrix[i][j] * v[j] for j in range(3)) for i in range(3)]
        num = sum(v[i] * mv[i] for i in range(3))
        den = sum(v[i] * v[i] for i in range(3))
        rayleighs.append(num / den)
    null_mode_error = max(abs(sum(row)) for row in matrix)
    checks = {
        "symmetric_matrix": symmetry_error == 0.0,
        "nonnegative_rayleigh": min(rayleighs) >= 0.0,
        "constant_mode_annihilated": null_mode_error == 0.0,
    }
    return Result(symmetry_error, min(rayleighs), null_mode_error, False, checks)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    result = build_result()
    payload = asdict(result)
    args.json_output.parent.mkdir(parents=True, exist_ok=True)
    args.json_output.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    if args.json:
        print(json.dumps(payload, indent=2, sort_keys=True))
    else:
        print(f"matrix_symmetry_error={result.matrix_symmetry_error}")
        print(f"promotion={result.promotion}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
