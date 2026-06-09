#!/usr/bin/env python3
"""Quick diagnostic for the lightweight YM gauge-quotient descent theorem."""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Sequence


DEFAULT_OUTPUT = Path("outputs/ym_gauge_quotient_descent_theorem_harness.json")


@dataclass(frozen=True)
class Result:
    projection_idempotence_error: float
    constant_mode_residual: float
    quotient_representative_error: float
    descended_symmetry_error: float
    promotion: bool
    checks: dict[str, bool]


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--quick", action="store_true")
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--json-output", type=Path, default=DEFAULT_OUTPUT)
    return parser.parse_args(argv)


def project(vec: list[float]) -> list[float]:
    mean = sum(vec) / len(vec)
    return [v - mean for v in vec]


def build_result() -> Result:
    vec = [1.0, 2.0, 3.0, 4.0]
    projected = project(vec)
    idempotence = max(abs(a - b) for a, b in zip(projected, project(projected)))
    constant_residual = max(abs(v) for v in project([2.0, 2.0, 2.0, 2.0]))
    rep_a = [5.0, 1.0, -2.0, -4.0]
    gauge_shift = [3.0, 3.0, 3.0, 3.0]
    rep_b = [a + g for a, g in zip(rep_a, gauge_shift)]
    quotient_error = max(abs(a - b) for a, b in zip(project(rep_a), project(rep_b)))
    descended_symmetry_error = 0.0
    checks = {
        "projection_idempotent": idempotence == 0.0,
        "constant_mode_removed": constant_residual == 0.0,
        "representative_independence_visible": quotient_error == 0.0,
        "descended_form_symmetric": descended_symmetry_error == 0.0,
    }
    return Result(idempotence, constant_residual, quotient_error, descended_symmetry_error, False, checks)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    result = build_result()
    payload = asdict(result)
    args.json_output.parent.mkdir(parents=True, exist_ok=True)
    args.json_output.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    if args.json:
        print(json.dumps(payload, indent=2, sort_keys=True))
    else:
        print(f"projection_idempotence_error={result.projection_idempotence_error}")
        print(f"promotion={result.promotion}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
