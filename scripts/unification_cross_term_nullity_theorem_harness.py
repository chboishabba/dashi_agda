#!/usr/bin/env python3
"""Fast diagnostic harness for the lightweight U-1a cross-term theorem."""

from __future__ import annotations

import argparse
import json
import random
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Callable, Sequence


DEFAULT_OUTPUT = Path("outputs/unification_cross_term_nullity_theorem_harness.json")
Vector = list[float]
Gluing = Callable[[Vector, int], Vector]


def add(x: Vector, y: Vector) -> Vector:
    return [a + b for a, b in zip(x, y)]


def sub(x: Vector, y: Vector) -> Vector:
    return [a - b for a, b in zip(x, y)]


def quotient(x: Vector, dim: int) -> Vector:
    return list(x[:dim])


def null_part(x: Vector, dim: int) -> Vector:
    return list(x[dim:])


def l_inf(x: Vector) -> float:
    return max((abs(v) for v in x), default=0.0)


def representative(rng: random.Random, dim: int) -> Vector:
    return [rng.uniform(-1.0, 1.0) for _ in range(2 * dim)]


def linear_quotient_gluing(x: Vector, dim: int) -> Vector:
    q = quotient(x, dim)
    return [1.1 * q[i] + 0.05 * q[(i + 1) % dim] for i in range(dim)] + [0.0] * dim


def quotient_plus_null_residual_gluing(x: Vector, dim: int) -> Vector:
    q = quotient(x, dim)
    n = null_part(x, dim)
    return (
        [0.9 * q[i] - 0.1 * q[(i + 1) % dim] for i in range(dim)]
        + [0.17 * q[i] * q[(i + 1) % dim] + 0.04 * n[i] for i in range(dim)]
    )


def nonlinear_quotient_gluing(x: Vector, dim: int) -> Vector:
    q = quotient(x, dim)
    out = [q[i] for i in range(dim)]
    out[0] += 0.25 * q[0] * q[-1]
    return out + [0.0] * dim


def cross_term(gluing: Gluing, x: Vector, y: Vector, dim: int) -> Vector:
    return sub(sub(gluing(add(x, y), dim), gluing(x, dim)), gluing(y, dim))


@dataclass(frozen=True)
class FamilyResult:
    name: str
    expected_cross_term_null: bool
    max_quotient_cross_term: float
    max_null_cross_term: float
    quotient_transport_error: float
    observed_cross_term_null: bool


@dataclass(frozen=True)
class HarnessResult:
    seed: int
    dimension: int
    samples: int
    families: list[FamilyResult]
    promotion: bool
    four_point_promotion: bool
    terminal_promotion: bool


def sample_family(
    rng: random.Random,
    dim: int,
    samples: int,
    name: str,
    expected_cross_term_null: bool,
    gluing: Gluing,
) -> FamilyResult:
    quotient_errors: list[float] = []
    null_errors: list[float] = []
    transport_errors: list[float] = []
    for _ in range(samples):
        x = representative(rng, dim)
        y = representative(rng, dim)
        ct = cross_term(gluing, x, y, dim)
        q = quotient(ct, dim)
        n = null_part(ct, dim)
        quotient_errors.append(l_inf(q))
        null_errors.append(l_inf(n))
        transport_errors.append(l_inf(q))
    max_q = max(quotient_errors, default=0.0)
    max_n = max(null_errors, default=0.0)
    observed = max_q < 1.0e-10
    return FamilyResult(
        name=name,
        expected_cross_term_null=expected_cross_term_null,
        max_quotient_cross_term=max_q,
        max_null_cross_term=max_n,
        quotient_transport_error=max(transport_errors, default=0.0),
        observed_cross_term_null=observed,
    )


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--seed", type=int, default=166)
    parser.add_argument("--dimension", type=int, default=3)
    parser.add_argument("--samples", type=int, default=120)
    parser.add_argument("--quick", action="store_true")
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--json-output", type=Path, default=DEFAULT_OUTPUT)
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    rng = random.Random(args.seed)
    samples = 24 if args.quick else args.samples
    dim = 2 if args.quick else args.dimension

    families = [
        sample_family(rng, dim, samples, "linear_quotient", True, linear_quotient_gluing),
        sample_family(
            rng, dim, samples, "quotient_plus_null_residual", True, quotient_plus_null_residual_gluing
        ),
        sample_family(rng, dim, samples, "nonlinear_quotient", False, nonlinear_quotient_gluing),
    ]

    payload = asdict(
        HarnessResult(
            seed=args.seed,
            dimension=dim,
            samples=samples,
            families=families,
            promotion=False,
            four_point_promotion=False,
            terminal_promotion=False,
        )
    )
    args.json_output.parent.mkdir(parents=True, exist_ok=True)
    args.json_output.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    if args.json:
        print(json.dumps(payload, indent=2, sort_keys=True))
    else:
        print(f"families={len(families)}")
        print(f"promotion={payload['promotion']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
