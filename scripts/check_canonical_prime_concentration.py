#!/usr/bin/env python3
"""Inspect exponent-level canonical prime concentration on a MoonshinePrimeState."""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict
from pathlib import Path

from moonshine_prime_object import SSP_PRIMES, observe, parse_state


def concentration_report(payload: dict) -> dict:
    state = parse_state(payload)
    observable = observe(state)
    weights = {int(p): int(state.factor_vector[p]) for p in SSP_PRIMES}
    max_weight = max(weights.values()) if weights else 0
    dominant_primes = [p for p in SSP_PRIMES if weights[p] == max_weight]
    signature_support = [p for p in SSP_PRIMES if bool(state.signature[p])]
    dominant_signature_overlap = [p for p in dominant_primes if state.signature[p]]

    return {
        "canonical_primes": list(SSP_PRIMES),
        "weights": weights,
        "max_weight": max_weight,
        "dominant_primes": dominant_primes,
        "dominant_prime_count": len(dominant_primes),
        "signature_support": signature_support,
        "dominant_signature_overlap": dominant_signature_overlap,
        "factor_support": list(observable.factor_support),
        "factor_support_weight": int(observable.factor_support_weight),
        "mdl_denominator": int(observable.mdl_denominator),
        "basin_label": observable.basin_label,
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
    print(json.dumps(report, indent=2 if args.pretty else None, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
