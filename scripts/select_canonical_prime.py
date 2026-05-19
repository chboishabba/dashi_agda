#!/usr/bin/env python3
"""Select the current canonical prime from a MoonshinePrimeState payload."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from check_canonical_prime_concentration import concentration_report


def select_from_report(report: dict) -> dict:
    dominant_primes = [int(p) for p in report.get("dominant_primes", [])]
    selected_prime = min(dominant_primes) if dominant_primes else None
    weights = {int(k): int(v) for k, v in report.get("weights", {}).items()}

    return {
        "selected_prime": selected_prime,
        "selected_weight": weights.get(selected_prime, 0) if selected_prime is not None else None,
        "tie_count": len(dominant_primes),
        "dominant_primes": dominant_primes,
        "selection_mode": "highest_exponent_lowest_prime_tiebreak",
        "max_weight": int(report.get("max_weight", 0)),
        "basin_label": report.get("basin_label", ""),
        "mdl_denominator": int(report.get("mdl_denominator", 0)),
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", help="Path to a MoonshinePrimeState JSON file")
    parser.add_argument("--pretty", action="store_true", help="Pretty-print JSON")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    payload = json.loads(Path(args.input).read_text())
    report = concentration_report(payload)
    selected = select_from_report(report)
    print(json.dumps(selected, indent=2 if args.pretty else None, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
