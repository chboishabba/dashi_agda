#!/usr/bin/env python3
"""Search exact dyadic Yang--Mills majorant regions.

The defaults mirror BalabanDyadicQuantitativeRegionExact.agda.  Every
calculation uses fractions.Fraction; floating point arithmetic is forbidden.
The coefficients are candidate majorants only until the physical Wilson,
patch, and seven-component derivations are connected.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from fractions import Fraction
from pathlib import Path
from typing import Iterable


@dataclass(frozen=True)
class QuadraticMajorant:
    linear: int
    quadratic: int

    def evaluate(self, radius: Fraction) -> Fraction:
        return self.linear * radius + self.quadratic * radius * radius


HESSIAN_DEFAULTS = {
    "curvature": QuadraticMajorant(64, 64),
    "transport": QuadraticMajorant(8, 4),
    "chart": QuadraticMajorant(16, 32),
    "gauge_fixing": QuadraticMajorant(32, 64),
    "block_constraint": QuadraticMajorant(16, 64),
}

NONLINEAR_DEFAULTS = {
    "bch": QuadraticMajorant(2, 2),
    "commutator": QuadraticMajorant(3, 2),
    "transport": QuadraticMajorant(2, 2),
    "background_derivative": QuadraticMajorant(4, 3),
    "gauge_fixing": QuadraticMajorant(3, 2),
    "block_constraint": QuadraticMajorant(3, 2),
    "chart_change": QuadraticMajorant(4, 2),
}

PATCH_DEFAULTS = {
    "bulk": Fraction(80, 1000),
    "boundary": Fraction(90, 1000),
    "interface": Fraction(95, 1000),
    "corner": Fraction(90, 1000),
    "nested": Fraction(95, 1000),
}


def sum_majorants(
    majorants: Iterable[QuadraticMajorant], radius: Fraction
) -> Fraction:
    return sum((majorant.evaluate(radius) for majorant in majorants), Fraction(0))


def fraction_json(value: Fraction) -> dict[str, int | str]:
    return {
        "numerator": value.numerator,
        "denominator": value.denominator,
        "text": str(value),
    }


def search(max_exponent: int, green_constant: Fraction) -> dict[str, object]:
    patch_total = sum(PATCH_DEFAULTS.values(), Fraction(0))
    if not patch_total < 1:
        raise ValueError(f"patch allocation is not strict: {patch_total} >= 1")

    attempts: list[dict[str, object]] = []
    for exponent in range(1, max_exponent + 1):
        radius = Fraction(1, 2**exponent)
        hessian = sum_majorants(HESSIAN_DEFAULTS.values(), radius)
        nonlinear = green_constant * sum_majorants(
            NONLINEAR_DEFAULTS.values(), radius
        )
        accepted = hessian < 1 and nonlinear < 1
        attempts.append(
            {
                "exponent": exponent,
                "radius": fraction_json(radius),
                "hessian": fraction_json(hessian),
                "nonlinear": fraction_json(nonlinear),
                "accepted": accepted,
            }
        )
        if accepted:
            return {
                "status": "found",
                "exponent": exponent,
                "radius": fraction_json(radius),
                "hessian": fraction_json(hessian),
                "nonlinear": fraction_json(nonlinear),
                "patch_total": fraction_json(patch_total),
                "green_constant": fraction_json(green_constant),
                "hessian_coefficients": {
                    name: asdict(value) for name, value in HESSIAN_DEFAULTS.items()
                },
                "nonlinear_coefficients": {
                    name: asdict(value) for name, value in NONLINEAR_DEFAULTS.items()
                },
                "patch_allocations": {
                    name: fraction_json(value) for name, value in PATCH_DEFAULTS.items()
                },
                "attempts": attempts,
                "physical_coefficients_proved": False,
            }

    return {
        "status": "not-found",
        "max_exponent": max_exponent,
        "patch_total": fraction_json(patch_total),
        "green_constant": fraction_json(green_constant),
        "attempts": attempts,
        "physical_coefficients_proved": False,
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-exponent", type=int, default=32)
    parser.add_argument("--green-numerator", type=int, default=4)
    parser.add_argument("--green-denominator", type=int, default=1)
    parser.add_argument("--output", type=Path)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    if args.max_exponent < 1:
        raise SystemExit("--max-exponent must be positive")
    if args.green_denominator <= 0:
        raise SystemExit("--green-denominator must be positive")

    result = search(
        args.max_exponent,
        Fraction(args.green_numerator, args.green_denominator),
    )
    encoded = json.dumps(result, indent=2, sort_keys=True)
    if args.output:
        args.output.write_text(encoded + "\n", encoding="utf-8")
    print(encoded)
    if result["status"] != "found":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
