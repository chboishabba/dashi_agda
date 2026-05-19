#!/usr/bin/env python3
"""Cheap runtime check for the canonical 15-prime selection/signature bridge."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from moonshine_prime_object import SSP_PRIMES, observe, parse_state


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", help="Path to a MoonshinePrimeState JSON file")
    parser.add_argument("--pretty", action="store_true", help="Pretty-print JSON output")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    payload = json.loads(Path(args.input).read_text())
    state = parse_state(payload)
    obs = observe(state)

    factor_support = list(obs.factor_support)
    signature_support = [p for p in SSP_PRIMES if obs.signature[p]]

    result = {
        "canonical_primes": SSP_PRIMES,
        "factor_support": factor_support,
        "signature_support": signature_support,
        "factor_support_subset_canonical": all(p in SSP_PRIMES for p in factor_support),
        "signature_support_subset_canonical": all(p in SSP_PRIMES for p in signature_support),
        "factor_vector_keys_match_canonical": sorted(obs.factor_vector) == SSP_PRIMES,
        "signature_keys_match_canonical": sorted(obs.signature) == SSP_PRIMES,
        "support_overlap": [p for p in factor_support if p in signature_support],
        "factor_support_weight": obs.factor_support_weight,
        "basin_label": obs.basin_label,
        "mdl_denominator": obs.mdl_denominator,
    }

    print(json.dumps(result, indent=2 if args.pretty else None, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
