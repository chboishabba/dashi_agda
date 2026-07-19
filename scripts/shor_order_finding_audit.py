#!/usr/bin/env python3
"""Finite Shor order-finding/factor-extraction audit.

This is not a quantum simulator. It checks the exact classical arithmetic seam
that a successful quantum period-finding sample must feed:

  multiplicative order r of a mod N
  -> r even
  -> x = a^(r/2) mod N
  -> gcd(x-1, N) or gcd(x+1, N) is nontrivial.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Iterable


@dataclass(frozen=True)
class ShorAttempt:
    modulus: int
    base: int
    coprime: bool
    order: int | None
    order_even: bool
    half_power: int | None
    minus_factor: int | None
    plus_factor: int | None
    success: bool


def multiplicative_order(base: int, modulus: int) -> int | None:
    """Return the exact multiplicative order, or None when undefined."""
    if modulus <= 1 or math.gcd(base, modulus) != 1:
        return None

    residue = 1
    for exponent in range(1, modulus + 1):
        residue = (residue * base) % modulus
        if residue == 1:
            return exponent
    raise AssertionError(f"order search bound failed for a={base}, N={modulus}")


def shor_attempt(modulus: int, base: int) -> ShorAttempt:
    coprime = math.gcd(base, modulus) == 1
    order = multiplicative_order(base, modulus)
    if order is None:
        return ShorAttempt(
            modulus=modulus,
            base=base,
            coprime=coprime,
            order=None,
            order_even=False,
            half_power=None,
            minus_factor=None,
            plus_factor=None,
            success=False,
        )

    order_even = order % 2 == 0
    if not order_even:
        return ShorAttempt(
            modulus=modulus,
            base=base,
            coprime=True,
            order=order,
            order_even=False,
            half_power=None,
            minus_factor=None,
            plus_factor=None,
            success=False,
        )

    half_power = pow(base, order // 2, modulus)
    minus_factor = math.gcd(half_power - 1, modulus)
    plus_factor = math.gcd(half_power + 1, modulus)
    success = any(1 < factor < modulus for factor in (minus_factor, plus_factor))

    return ShorAttempt(
        modulus=modulus,
        base=base,
        coprime=True,
        order=order,
        order_even=True,
        half_power=half_power,
        minus_factor=minus_factor,
        plus_factor=plus_factor,
        success=success,
    )


def audit_modulus(modulus: int, bases: Iterable[int]) -> dict[str, object]:
    attempts = [shor_attempt(modulus, base) for base in bases]
    successes = [attempt for attempt in attempts if attempt.success]
    return {
        "modulus": modulus,
        "attempt_count": len(attempts),
        "success_count": len(successes),
        "success_rate": len(successes) / len(attempts) if attempts else 0.0,
        "attempts": [asdict(attempt) for attempt in attempts],
    }


def parse_int_csv(value: str) -> list[int]:
    values = [int(item.strip()) for item in value.split(",") if item.strip()]
    if not values:
        raise argparse.ArgumentTypeError("expected at least one integer")
    return values


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--moduli",
        type=parse_int_csv,
        default=[15, 21, 33, 35, 55],
        help="comma-separated composite moduli",
    )
    parser.add_argument(
        "--max-base",
        type=int,
        default=12,
        help="audit bases 2..max-base inclusive",
    )
    parser.add_argument("--output-json", type=Path)
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args()

    if args.max_base < 2:
        parser.error("--max-base must be at least 2")

    reports = [
        audit_modulus(modulus, range(2, min(args.max_base, modulus - 1) + 1))
        for modulus in args.moduli
    ]

    concrete_witnesses = {
        "N15_a2": asdict(shor_attempt(15, 2)),
        "N21_a2": asdict(shor_attempt(21, 2)),
    }

    payload = {
        "algorithm": "finite classical seam of Shor order finding",
        "moduli": reports,
        "concrete_witnesses": concrete_witnesses,
        "all_concrete_witnesses_succeed": all(
            witness["success"] for witness in concrete_witnesses.values()
        ),
        "authority": {
            "finite_arithmetic_checked": True,
            "quantum_sampling_distribution_proved": False,
            "continued_fraction_probability_bound_proved": False,
            "physical_quantum_hardware_claimed": False,
        },
    }

    rendered = json.dumps(payload, indent=2 if args.pretty else None, sort_keys=True)
    if args.output_json:
        args.output_json.write_text(rendered + "\n", encoding="utf-8")
    print(rendered)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
