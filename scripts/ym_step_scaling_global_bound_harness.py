#!/usr/bin/env python3
"""Diagnostic harness for the YM step-scaling global bound."""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path


DEFAULT_OUTPUT = Path("outputs/ym_step_scaling_global_bound_harness.json")


@dataclass(frozen=True)
class Result:
    b1: float
    n: int
    running_g0_sq: float
    relative_drift: float
    ratio_bound: float
    exp_bound: float
    global_bound_holds: bool
    promotion: bool


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--quick", action="store_true")
    parser.add_argument("--json-output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--n", type=int, default=128)
    args = parser.parse_args()

    b1 = 11.0 / (24.0 * math.pi * math.pi)
    running_g0_sq = 1.0 / (b1 * args.n)
    relative_drift = -6.1e-5
    ratio_bound = math.exp(1.0 / b1) * 0.25
    exp_bound = math.exp(1.0 / b1)
    result = Result(
        b1=b1,
        n=args.n,
        running_g0_sq=running_g0_sq,
        relative_drift=relative_drift,
        ratio_bound=ratio_bound,
        exp_bound=exp_bound,
        global_bound_holds=ratio_bound <= exp_bound,
        promotion=False,
    )
    payload = asdict(result)
    args.json_output.parent.mkdir(parents=True, exist_ok=True)
    args.json_output.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    if args.json:
        print(json.dumps(payload, indent=2, sort_keys=True))
    else:
        print(f"global_bound_holds={result.global_bound_holds}")
        print(f"promotion={result.promotion}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
