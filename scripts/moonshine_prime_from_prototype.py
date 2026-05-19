#!/usr/bin/env python3
"""Adapt emitted prototype state JSON into a MoonshinePrimeState payload."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from moonshine_prime_object import SSP_PRIMES


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", help="Path to an emitted prototype state JSON file")
    parser.add_argument("--output", help="Optional path for MoonshinePrimeState JSON")
    parser.add_argument("--pretty", action="store_true")
    return parser.parse_args()


def prime_valuation_integer(n: int, p: int) -> int:
    n = abs(n)
    if n == 0:
        return 0
    v = 0
    while n % p == 0:
        n //= p
        v += 1
    return v


def quantize_delta(delta: list[float], scale: float = 1000.0) -> list[int]:
    return [int(round(x * scale)) for x in delta]


def factor_vector_from_delta(delta: list[float]) -> dict[int, int]:
    qdelta = quantize_delta(delta)
    return {
        p: sum(prime_valuation_integer(component, p) for component in qdelta)
        for p in SSP_PRIMES
    }


def signature_from_factor_vector(factors: dict[int, int]) -> dict[int, bool]:
    return {p: factors[p] > 0 for p in SSP_PRIMES}


def eigen_profile_from_signature(signature: dict[int, bool]) -> dict[str, int]:
    primes = list(SSP_PRIMES)
    earth = sum(1 for p in primes[:5] if signature[p])
    spoke = sum(1 for p in primes[5:10] if signature[p])
    hub = sum(1 for p in primes[10:] if signature[p])
    return {"earth": earth, "spoke": spoke, "hub": hub}


def basin_label_from_payload(payload: dict[str, Any]) -> str:
    admissibility = payload.get("admissibility", {})
    if admissibility.get("basin_expected"):
        return "canonical"
    return "noncanonical"


def adapt(payload: dict[str, Any]) -> dict[str, Any]:
    delta = payload["delta"]
    mdl_level = int(round(float(payload.get("mdl_level", 0.0))))
    factors = factor_vector_from_delta(delta)
    signature = signature_from_factor_vector(factors)
    eigen = eigen_profile_from_signature(signature)

    return {
        "carrier": [int(round(float(x) * 1000.0)) for x in delta],
        "signature": {str(p): signature[p] for p in SSP_PRIMES},
        "eigenProfile": eigen,
        "basinLabel": basin_label_from_payload(payload),
        "factorVector": {str(p): factors[p] for p in SSP_PRIMES},
        "mdlLevel": mdl_level,
        "provenance": {
            "adapter": "moonshine_prime_from_prototype",
            "source_trace_id": payload.get("trace_id"),
            "source_provenance": payload.get("provenance", {}),
        },
    }


def main() -> int:
    args = parse_args()
    payload = json.loads(Path(args.input).read_text())
    adapted = adapt(payload)
    text = json.dumps(adapted, indent=2 if args.pretty else None, sort_keys=True)
    if args.output:
        Path(args.output).write_text(text + ("\n" if args.pretty else ""))
    else:
        print(text)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
