#!/usr/bin/env python3
"""Deterministic harness for the corrected U-1a-H boundary.

This diagnostic compares:

* quadratic families where the explicit U-1a-H hypothesis holds and the
  four-point/parallelogram residual vanishes;
* nonquadratic but still 2-homogeneous counterexamples, showing why
  2-homogeneity alone is insufficient;
* hypothesis-only nonlinear examples, showing that U-1a-H on its own does not
  yet certify the downstream quadratic consumer.

The output is diagnostic only and always keeps promotion=false.
"""

from __future__ import annotations

import argparse
import json
import math
import random
import statistics
from dataclasses import asdict, dataclass
from typing import Callable, Sequence


Vector = list[float]
Matrix = list[list[float]]
Map = Callable[[Vector, Matrix], Vector]
CrossTermBilinear = Callable[[Vector, Vector, Matrix], Vector]
Quadratic = Callable[[Vector], float]


def add(x: Sequence[float], y: Sequence[float]) -> Vector:
    return [a + b for a, b in zip(x, y)]


def sub(x: Sequence[float], y: Sequence[float]) -> Vector:
    return [a - b for a, b in zip(x, y)]


def scale(alpha: float, x: Sequence[float]) -> Vector:
    return [alpha * value for value in x]


def dot(x: Sequence[float], y: Sequence[float]) -> float:
    return sum(a * b for a, b in zip(x, y))


def l2_norm(x: Sequence[float]) -> float:
    return math.sqrt(max(0.0, dot(x, x)))


def mat_vec(matrix: Matrix, x: Sequence[float]) -> Vector:
    return [dot(row, x) for row in matrix]


def symmetric_matrix(dim: int) -> Matrix:
    matrix: Matrix = []
    for i in range(dim):
        row: Vector = []
        for j in range(dim):
            diagonal = 1.2 if i == j else 0.0
            coupling = 0.05 * (i + 1) * (j + 1) / max(1, dim)
            parity = 0.01 * ((-1.0) ** (i + j))
            row.append(diagonal + coupling + parity)
        matrix.append(row)
    return matrix


def representative(rng: random.Random, dim: int) -> Vector:
    return [rng.uniform(-1.1, 1.1) for _ in range(dim)]


def linear_map(x: Vector, matrix: Matrix) -> Vector:
    return mat_vec(matrix, x)


def zero_bilinear(x: Vector, y: Vector, matrix: Matrix) -> Vector:
    return [0.0 for _ in x]


def weighted_l2(dim: int) -> Quadratic:
    weights = [1.0 + 0.15 * i for i in range(dim)]

    def energy(x: Vector) -> float:
        return sum(weight * value * value for weight, value in zip(weights, x))

    return energy


def l2_quadratic(x: Vector) -> float:
    return dot(x, x)


def nonlinear_componentwise_map(x: Vector, matrix: Matrix) -> Vector:
    linear = mat_vec(matrix, x)
    return [base + 0.35 * value * value for base, value in zip(linear, x)]


def nonlinear_componentwise_bilinear(x: Vector, y: Vector, matrix: Matrix) -> Vector:
    return [0.35 * a * b for a, b in zip(x, y)]


def l1_squared(x: Vector) -> float:
    return sum(abs(value) for value in x) ** 2


def p3_norm_squared(x: Vector) -> float:
    return sum(abs(value) ** 3.0 for value in x) ** (2.0 / 3.0)


def max_norm_squared(x: Vector) -> float:
    return max(abs(value) for value in x) ** 2


def cross_term(g_map: Map, x: Vector, y: Vector, matrix: Matrix) -> Vector:
    return sub(sub(g_map(add(x, y), matrix), g_map(x, matrix)), g_map(y, matrix))


def four_point_residual(q: Quadratic, g_map: Map, x: Vector, y: Vector, matrix: Matrix) -> float:
    return (
        q(g_map(add(x, y), matrix))
        + q(g_map(sub(x, y), matrix))
        - 2.0 * q(g_map(x, matrix))
        - 2.0 * q(g_map(y, matrix))
    )


def two_homogeneity_error(q: Quadratic, x: Vector) -> float:
    return abs(q(scale(2.0, x)) - 4.0 * q(x))


def symmetry_error(bilinear: CrossTermBilinear, x: Vector, y: Vector, matrix: Matrix) -> float:
    return l2_norm(sub(bilinear(x, y, matrix), bilinear(y, x, matrix)))


@dataclass(frozen=True)
class Family:
    name: str
    expected: str
    g_map: Map
    bilinear: CrossTermBilinear
    quadratic: Quadratic
    should_satisfy_hypothesis: bool
    should_satisfy_four_point: bool


@dataclass(frozen=True)
class Metrics:
    name: str
    expected: str
    hypothesis_pass: bool
    four_point_pass: bool
    two_homogeneous_pass: bool
    expected_outcome_observed: bool
    mean_cross_term_residual: float
    max_cross_term_residual: float
    mean_symmetry_error: float
    max_symmetry_error: float
    mean_four_point_residual: float
    max_four_point_residual: float
    mean_two_homogeneity_error: float
    max_two_homogeneity_error: float
    witness_count: int
    worst_witnesses: list[dict[str, object]]


def percentile(values: Sequence[float], q: float) -> float:
    if not values:
        return 0.0
    ordered = sorted(values)
    index = min(len(ordered) - 1, max(0, math.ceil(q * len(ordered)) - 1))
    return ordered[index]


def evaluate_family(
    family: Family,
    xs: Sequence[Vector],
    ys: Sequence[Vector],
    matrix: Matrix,
    tolerance: float,
    witness_limit: int,
) -> Metrics:
    cross_term_residuals: list[float] = []
    symmetry_residuals: list[float] = []
    four_point_residuals: list[float] = []
    homogeneity_errors: list[float] = []
    witnesses: list[dict[str, object]] = []

    for index, (x, y) in enumerate(zip(xs, ys)):
        actual = cross_term(family.g_map, x, y, matrix)
        expected = scale(2.0, family.bilinear(x, y, matrix))
        cross_residual = l2_norm(sub(actual, expected))
        symmetry_residual = symmetry_error(family.bilinear, x, y, matrix)
        four_point = abs(four_point_residual(family.quadratic, family.g_map, x, y, matrix))
        homogeneity = two_homogeneity_error(family.quadratic, family.g_map(x, matrix))

        cross_term_residuals.append(cross_residual)
        symmetry_residuals.append(symmetry_residual)
        four_point_residuals.append(four_point)
        homogeneity_errors.append(homogeneity)

        combined = cross_residual + symmetry_residual + four_point + homogeneity
        if combined > tolerance:
            witnesses.append(
                {
                    "sample": index,
                    "combined_error": combined,
                    "cross_term_residual": cross_residual,
                    "symmetry_error": symmetry_residual,
                    "four_point_residual": four_point,
                    "two_homogeneity_error": homogeneity,
                    "x": list(x),
                    "y": list(y),
                    "actual_cross_term": actual,
                    "expected_two_b": expected,
                }
            )
            witnesses.sort(key=lambda item: float(item["combined_error"]), reverse=True)
            del witnesses[witness_limit:]

    hypothesis_pass = (
        max(cross_term_residuals, default=0.0) <= tolerance
        and max(symmetry_residuals, default=0.0) <= tolerance
    )
    four_point_pass = max(four_point_residuals, default=0.0) <= tolerance
    two_homogeneous_pass = max(homogeneity_errors, default=0.0) <= tolerance
    expected_outcome_observed = (
        hypothesis_pass == family.should_satisfy_hypothesis
        and four_point_pass == family.should_satisfy_four_point
    )

    return Metrics(
        name=family.name,
        expected=family.expected,
        hypothesis_pass=hypothesis_pass,
        four_point_pass=four_point_pass,
        two_homogeneous_pass=two_homogeneous_pass,
        expected_outcome_observed=expected_outcome_observed,
        mean_cross_term_residual=statistics.fmean(cross_term_residuals) if cross_term_residuals else 0.0,
        max_cross_term_residual=max(cross_term_residuals) if cross_term_residuals else 0.0,
        mean_symmetry_error=statistics.fmean(symmetry_residuals) if symmetry_residuals else 0.0,
        max_symmetry_error=max(symmetry_residuals) if symmetry_residuals else 0.0,
        mean_four_point_residual=statistics.fmean(four_point_residuals) if four_point_residuals else 0.0,
        max_four_point_residual=max(four_point_residuals) if four_point_residuals else 0.0,
        mean_two_homogeneity_error=statistics.fmean(homogeneity_errors) if homogeneity_errors else 0.0,
        max_two_homogeneity_error=max(homogeneity_errors) if homogeneity_errors else 0.0,
        witness_count=len(witnesses),
        worst_witnesses=witnesses,
    )


def build_families(dim: int) -> list[Family]:
    return [
        Family(
            name="linear_weighted_quadratic_pass",
            expected="pass: linear G, zero bilinear witness, weighted quadratic consumer",
            g_map=linear_map,
            bilinear=zero_bilinear,
            quadratic=weighted_l2(dim),
            should_satisfy_hypothesis=True,
            should_satisfy_four_point=True,
        ),
        Family(
            name="linear_l2_pass",
            expected="pass: linear G, zero bilinear witness, l2 quadratic consumer",
            g_map=linear_map,
            bilinear=zero_bilinear,
            quadratic=l2_quadratic,
            should_satisfy_hypothesis=True,
            should_satisfy_four_point=True,
        ),
        Family(
            name="nonlinear_hypothesis_only_componentwise",
            expected="mixed: U-1a-H holds, but nonlinear G breaks the downstream quadratic consumer",
            g_map=nonlinear_componentwise_map,
            bilinear=nonlinear_componentwise_bilinear,
            quadratic=l2_quadratic,
            should_satisfy_hypothesis=True,
            should_satisfy_four_point=False,
        ),
        Family(
            name="l1_squared_counterexample",
            expected="fail downstream: 2-homogeneous nonquadratic consumer",
            g_map=linear_map,
            bilinear=zero_bilinear,
            quadratic=l1_squared,
            should_satisfy_hypothesis=True,
            should_satisfy_four_point=False,
        ),
        Family(
            name="p3_norm_squared_counterexample",
            expected="fail downstream: p=3 norm squared is 2-homogeneous but nonquadratic",
            g_map=linear_map,
            bilinear=zero_bilinear,
            quadratic=p3_norm_squared,
            should_satisfy_hypothesis=True,
            should_satisfy_four_point=False,
        ),
        Family(
            name="max_norm_squared_counterexample",
            expected="fail downstream: max norm squared is 2-homogeneous but nonquadratic",
            g_map=linear_map,
            bilinear=zero_bilinear,
            quadratic=max_norm_squared,
            should_satisfy_hypothesis=True,
            should_satisfy_four_point=False,
        ),
    ]


def run(samples: int, seed: int, dim: int, tolerance: float, witness_limit: int) -> dict[str, object]:
    rng = random.Random(seed)
    xs = [representative(rng, dim) for _ in range(samples)]
    ys = [representative(rng, dim) for _ in range(samples)]
    matrix = symmetric_matrix(dim)
    results = [
        evaluate_family(family, xs, ys, matrix, tolerance, witness_limit)
        for family in build_families(dim)
    ]

    return {
        "ok": all(result.expected_outcome_observed for result in results),
        "samples": samples,
        "seed": seed,
        "dimension": dim,
        "tolerance": tolerance,
        "families": [asdict(result) for result in results],
        "hypothesis_satisfying_families": [
            result.name for result in results if result.hypothesis_pass
        ],
        "four_point_failing_families": [
            result.name for result in results if not result.four_point_pass
        ],
        "residual_summary": {
            "max_cross_term_residual": max((result.max_cross_term_residual for result in results), default=0.0),
            "max_symmetry_error": max((result.max_symmetry_error for result in results), default=0.0),
            "max_four_point_residual": max((result.max_four_point_residual for result in results), default=0.0),
            "p95_four_point_residual": percentile(
                [result.max_four_point_residual for result in results],
                0.95,
            ),
        },
        "interpretation": {
            "hypothesis_u1a_h_required": True,
            "two_homogeneity_alone_sufficient": False,
            "nonquadratic_two_homogeneous_counterexamples_detected": True,
            "nonlinear_hypothesis_only_family_detected": True,
        },
        "promotion": False,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--samples", type=int, default=2000)
    parser.add_argument("--seed", type=int, default=20260609)
    parser.add_argument("--dimension", type=int, default=4)
    parser.add_argument("--tolerance", type=float, default=1.0e-9)
    parser.add_argument("--witness-limit", type=int, default=3)
    parser.add_argument("--json-output")
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()

    if args.samples <= 0:
        raise SystemExit("--samples must be positive")
    if args.dimension <= 1:
        raise SystemExit("--dimension must be at least 2")
    if args.witness_limit < 0:
        raise SystemExit("--witness-limit must be nonnegative")

    payload = run(
        samples=args.samples,
        seed=args.seed,
        dim=args.dimension,
        tolerance=args.tolerance,
        witness_limit=args.witness_limit,
    )
    if args.json_output:
        with open(args.json_output, "w", encoding="utf-8") as handle:
            json.dump(payload, handle, indent=2, sort_keys=True)
            handle.write("\n")
    if args.json:
        print(json.dumps(payload, indent=2, sort_keys=True))
    else:
        print(
            "ok={ok} passing_hypothesis={count} failing_four_point={fails}".format(
                ok=payload["ok"],
                count=len(payload["hypothesis_satisfying_families"]),
                fails=",".join(payload["four_point_failing_families"]),
            )
        )
    return 0 if payload["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
