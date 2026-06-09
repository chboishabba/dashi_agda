#!/usr/bin/env python3
"""Quick diagnostic for the lightweight unification null-class stability theorem."""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Sequence


DEFAULT_OUTPUT = Path("outputs/unification_null_class_stability_theorem_harness.json")
EPS = 1.0e-12


@dataclass(frozen=True)
class Result:
    additive_closure_error: float
    negation_closure_error: float
    representative_invariance_error: float
    promotion: bool
    checks: dict[str, bool]


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--quick", action="store_true")
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--json-output", type=Path, default=DEFAULT_OUTPUT)
    return parser.parse_args(argv)


def build_result() -> Result:
    n1 = [0.1, -0.2]
    n2 = [0.05, 0.15]
    additive_error = max(abs(a + b - c) for a, b, c in zip(n1, n2, [0.15, -0.05]))
    negation_error = max(abs(a + b) for a, b in zip(n1, [-0.1, 0.2]))
    base = [1.0, 2.0, 0.1, -0.2]
    rep = [1.0, 2.0, 0.4, 0.7]
    representative_error = max(abs(a - b) for a, b in zip(base[:2], rep[:2]))
    checks = {
        "additive_closure": additive_error <= EPS,
        "negation_closure": negation_error <= EPS,
        "representative_invariance_visible": representative_error <= EPS,
    }
    return Result(additive_error, negation_error, representative_error, False, checks)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    result = build_result()
    payload = asdict(result)
    args.json_output.parent.mkdir(parents=True, exist_ok=True)
    args.json_output.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    if args.json:
        print(json.dumps(payload, indent=2, sort_keys=True))
    else:
        print(f"additive_closure_error={result.additive_closure_error}")
        print(f"promotion={result.promotion}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
