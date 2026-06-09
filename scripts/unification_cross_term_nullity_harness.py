#!/usr/bin/env python3
"""Finite diagnostic harness for the U-1a cross-term nullity target.

The Agda boundary names the missing theorem:

    C(s1, s2) = G(s1 + s2) - G(s1) - G(s2) lies in nullClass.

This pure-stdlib harness samples finite representative vectors split into
quotient and null coordinates.  It checks the local cross-term residual and the
downstream four-point/parallelogram residual for several families:

* quadratic / gluing-linear defects should pass;
* gluing with nonlinear null-only residual should still pass modulo null;
* l1, p=3, and coupled nonquadratic defects show that cross-term nullity alone
  does not force four-point cancellation;
* nonlinear quotient gluing fails the U-1a cross-term target itself.

It is a falsification/diagnostic surface only and always emits promotion=false.
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
Gluing = Callable[[Vector, Matrix, int], Vector]
Energy = Callable[[Vector], float]


def add(x: Sequence[float], y: Sequence[float]) -> Vector:
    return [a + b for a, b in zip(x, y)]


def sub(x: Sequence[float], y: Sequence[float]) -> Vector:
    return [a - b for a, b in zip(x, y)]


def scale(alpha: float, x: Sequence[float]) -> Vector:
    return [alpha * value for value in x]


def dot(x: Sequence[float], y: Sequence[float]) -> float:
    return sum(a * b for a, b in zip(x, y))


def l2_sq(x: Sequence[float]) -> float:
    return dot(x, x)


def l2_norm(x: Sequence[float]) -> float:
    return math.sqrt(max(0.0, l2_sq(x)))


def quotient(x: Sequence[float], dim: int) -> Vector:
    return list(x[:dim])


def null_part(x: Sequence[float], dim: int) -> Vector:
    return list(x[dim:])


def mat_vec(matrix: Matrix, vector: Sequence[float]) -> Vector:
    return [dot(row, vector) for row in matrix]


def deterministic_matrix(dim: int) -> Matrix:
    matrix: Matrix = []
    for i in range(dim):
        row: Vector = []
        for j in range(dim):
            diagonal = 1.0 + 0.07 * (i + 1) if i == j else 0.0
            symmetric = 0.025 * (i + 1) * (j + 2) / max(1, dim)
            alternating = 0.011 * ((-1.0) ** (i + j)) * (1 + abs(i - j))
            row.append(diagonal + symmetric + alternating)
        matrix.append(row)
    return matrix


def representative(rng: random.Random, dim: int) -> Vector:
    q = [rng.uniform(-1.3, 1.3) for _ in range(dim)]
    n = [rng.uniform(-0.9, 0.9) for _ in range(dim)]
    return q + n


def linear_quotient_gluing(x: Vector, matrix: Matrix, dim: int) -> Vector:
    return mat_vec(matrix, quotient(x, dim)) + [0.0] * dim


def linear_with_null_channel_gluing(x: Vector, matrix: Matrix, dim: int) -> Vector:
    q = quotient(x, dim)
    n = null_part(x, dim)
    null = [0.23 * q[i] - 0.17 * n[i] for i in range(dim)]
    return mat_vec(matrix, q) + null


def null_residual_gluing(x: Vector, matrix: Matrix, dim: int) -> Vector:
    q = quotient(x, dim)
    n = null_part(x, dim)
    quotient_out = mat_vec(matrix, q)
    null_out: Vector = []
    for i in range(dim):
        left = q[i]
        right = q[(i + 1) % dim]
        null_out.append(0.19 * left * right + 0.07 * n[i] * n[i])
    return quotient_out + null_out


def nonlinear_quotient_gluing(x: Vector, matrix: Matrix, dim: int) -> Vector:
    q = quotient(x, dim)
    out = mat_vec(matrix, q)
    if out:
        out[0] += 0.31 * q[0] * q[-1]
    if len(out) > 1:
        out[1] -= 0.21 * q[0] * q[0]
    return out + [0.0] * dim


def quadratic_energy(gx: Vector) -> float:
    return l2_sq(gx)


def quotient_quadratic_energy(dim: int) -> Energy:
    def energy(gx: Vector) -> float:
        return l2_sq(quotient(gx, dim))

    return energy


def l1_squared_energy(gx: Vector) -> float:
    return sum(abs(value) for value in gx) ** 2


def p3_norm_squared_energy(gx: Vector) -> float:
    return sum(abs(value) ** 3.0 for value in gx) ** (2.0 / 3.0)


def coupled_nonquadratic_energy(gx: Vector) -> float:
    base = l2_sq(gx)
    coupling = sum((gx[i] * gx[i + 1]) ** 2 for i in range(len(gx) - 1))
    return base + 0.18 * coupling


@dataclass(frozen=True)
class Family:
    name: str
    expected: str
    gluing: Gluing
    energy: Energy
    should_cross_term_be_null: bool
    should_four_point_cancel: bool


@dataclass(frozen=True)
class SampleRow:
    cross_term_mod_null_residual: float
    cross_term_total_norm: float
    four_point_defect: float
    two_homogeneity_error: float
    combined_error: float


@dataclass(frozen=True)
class FamilyMetrics:
    name: str
    expected: str
    observed_pass: bool
    expected_outcome_observed: bool
    cross_term_null_pass: bool
    four_point_cancel_pass: bool
    two_homogeneous_pass: bool
    mean_modulo_null_residual: float
    max_modulo_null_residual: float
    p95_modulo_null_residual: float
    mean_abs_four_point_defect: float
    max_abs_four_point_defect: float
    p95_abs_four_point_defect: float
    mean_two_homogeneity_error: float
    max_two_homogeneity_error: float
    failed_checks: list[str]
    witness_count: int
    worst_witnesses: list[dict[str, object]]


def percentile(values: Sequence[float], q: float) -> float:
    if not values:
        return 0.0
    ordered = sorted(values)
    index = min(len(ordered) - 1, max(0, math.ceil(q * len(ordered)) - 1))
    return ordered[index]


def cross_term(gluing: Gluing, x: Vector, y: Vector, matrix: Matrix, dim: int) -> Vector:
    return sub(
        sub(gluing(add(x, y), matrix, dim), gluing(x, matrix, dim)),
        gluing(y, matrix, dim),
    )


def four_point_defect(
    gluing: Gluing,
    energy: Energy,
    x: Vector,
    y: Vector,
    matrix: Matrix,
    dim: int,
) -> float:
    return (
        energy(gluing(add(x, y), matrix, dim))
        + energy(gluing(sub(x, y), matrix, dim))
        - 2.0 * energy(gluing(x, matrix, dim))
        - 2.0 * energy(gluing(y, matrix, dim))
    )


def two_homogeneity_error(
    gluing: Gluing,
    energy: Energy,
    x: Vector,
    matrix: Matrix,
    dim: int,
) -> float:
    return abs(energy(gluing(scale(2.0, x), matrix, dim)) - 4.0 * energy(gluing(x, matrix, dim)))


def evaluate_family(
    family: Family,
    xs: Sequence[Vector],
    ys: Sequence[Vector],
    matrix: Matrix,
    dim: int,
    tolerance: float,
    witness_limit: int,
) -> FamilyMetrics:
    rows: list[SampleRow] = []
    witnesses: list[dict[str, object]] = []

    for index, (x, y) in enumerate(zip(xs, ys)):
        c = cross_term(family.gluing, x, y, matrix, dim)
        mod_residual = l2_norm(quotient(c, dim))
        total_norm = l2_norm(c)
        four_point = four_point_defect(family.gluing, family.energy, x, y, matrix, dim)
        hom_error = two_homogeneity_error(family.gluing, family.energy, x, matrix, dim)
        combined = mod_residual + abs(four_point) + hom_error
        row = SampleRow(
            cross_term_mod_null_residual=mod_residual,
            cross_term_total_norm=total_norm,
            four_point_defect=four_point,
            two_homogeneity_error=hom_error,
            combined_error=combined,
        )
        rows.append(row)
        if combined > tolerance:
            witnesses.append(
                {
                    "sample": index,
                    **asdict(row),
                    "quotient_x": quotient(x, dim),
                    "quotient_y": quotient(y, dim),
                    "cross_term_quotient": quotient(c, dim),
                    "cross_term_null": null_part(c, dim),
                }
            )
            witnesses.sort(key=lambda item: float(item["combined_error"]), reverse=True)
            del witnesses[witness_limit:]

    modulo_null_residuals = [row.cross_term_mod_null_residual for row in rows]
    four_point_residuals = [abs(row.four_point_defect) for row in rows]
    homogeneity_errors = [row.two_homogeneity_error for row in rows]

    cross_term_null_pass = max(modulo_null_residuals, default=0.0) <= tolerance
    four_point_cancel_pass = max(four_point_residuals, default=0.0) <= tolerance
    two_homogeneous_pass = max(homogeneity_errors, default=0.0) <= tolerance

    failed_checks: list[str] = []
    if not cross_term_null_pass:
        failed_checks.append("cross_term_not_null_modulo_quotient")
    if not two_homogeneous_pass:
        failed_checks.append("energy_not_two_homogeneous")
    if not four_point_cancel_pass:
        failed_checks.append("four_point_defect_nonzero")

    observed_pass = cross_term_null_pass and two_homogeneous_pass and four_point_cancel_pass
    expected_observed = (
        cross_term_null_pass == family.should_cross_term_be_null
        and four_point_cancel_pass == family.should_four_point_cancel
    )

    return FamilyMetrics(
        name=family.name,
        expected=family.expected,
        observed_pass=observed_pass,
        expected_outcome_observed=expected_observed,
        cross_term_null_pass=cross_term_null_pass,
        four_point_cancel_pass=four_point_cancel_pass,
        two_homogeneous_pass=two_homogeneous_pass,
        mean_modulo_null_residual=statistics.fmean(modulo_null_residuals)
        if modulo_null_residuals
        else 0.0,
        max_modulo_null_residual=max(modulo_null_residuals) if modulo_null_residuals else 0.0,
        p95_modulo_null_residual=percentile(modulo_null_residuals, 0.95),
        mean_abs_four_point_defect=statistics.fmean(four_point_residuals)
        if four_point_residuals
        else 0.0,
        max_abs_four_point_defect=max(four_point_residuals) if four_point_residuals else 0.0,
        p95_abs_four_point_defect=percentile(four_point_residuals, 0.95),
        mean_two_homogeneity_error=statistics.fmean(homogeneity_errors)
        if homogeneity_errors
        else 0.0,
        max_two_homogeneity_error=max(homogeneity_errors) if homogeneity_errors else 0.0,
        failed_checks=failed_checks,
        witness_count=len(witnesses),
        worst_witnesses=witnesses,
    )


def build_families(dim: int) -> list[Family]:
    quotient_quadratic = quotient_quadratic_energy(dim)
    return [
        Family(
            name="quadratic_linear_gluing",
            expected="pass: linear G has C=0 and quotient quadratic has zero four-point defect",
            gluing=linear_quotient_gluing,
            energy=quotient_quadratic,
            should_cross_term_be_null=True,
            should_four_point_cancel=True,
        ),
        Family(
            name="quadratic_linear_with_null_channel",
            expected="pass: linear null channel keeps C=0 and quadratic energy passes",
            gluing=linear_with_null_channel_gluing,
            energy=quadratic_energy,
            should_cross_term_be_null=True,
            should_four_point_cancel=True,
        ),
        Family(
            name="quadratic_null_residual_gluing",
            expected="pass modulo null: nonlinear C may be nonzero but only in null coordinates",
            gluing=null_residual_gluing,
            energy=quotient_quadratic,
            should_cross_term_be_null=True,
            should_four_point_cancel=True,
        ),
        Family(
            name="l1_squared_linear_gluing",
            expected="fail downstream: C=0 but l1 squared is not parallelogram/quadratic",
            gluing=linear_quotient_gluing,
            energy=l1_squared_energy,
            should_cross_term_be_null=True,
            should_four_point_cancel=False,
        ),
        Family(
            name="p3_norm_squared_linear_gluing",
            expected="fail downstream: C=0 but p=3 norm squared is not Hilbert quadratic",
            gluing=linear_quotient_gluing,
            energy=p3_norm_squared_energy,
            should_cross_term_be_null=True,
            should_four_point_cancel=False,
        ),
        Family(
            name="coupled_nonquadratic_linear_gluing",
            expected="fail downstream: C=0 but quartic coupling breaks four-point cancellation",
            gluing=linear_quotient_gluing,
            energy=coupled_nonquadratic_energy,
            should_cross_term_be_null=True,
            should_four_point_cancel=False,
        ),
        Family(
            name="nonlinear_quotient_gluing",
            expected="fail U-1a: C has quotient component and is not null",
            gluing=nonlinear_quotient_gluing,
            energy=quotient_quadratic,
            should_cross_term_be_null=False,
            should_four_point_cancel=False,
        ),
    ]


def run(samples: int, seed: int, dim: int, tolerance: float, witness_limit: int) -> dict[str, object]:
    rng = random.Random(seed)
    xs = [representative(rng, dim) for _ in range(samples)]
    ys = [representative(rng, dim) for _ in range(samples)]
    matrix = deterministic_matrix(dim)
    families = build_families(dim)
    results = [
        evaluate_family(family, xs, ys, matrix, dim, tolerance, witness_limit)
        for family in families
    ]

    expected_all_observed = all(result.expected_outcome_observed for result in results)
    passing = [result.name for result in results if result.observed_pass]
    failing = [result.name for result in results if not result.observed_pass]
    cross_term_pass_four_point_fail = [
        result.name
        for result in results
        if result.cross_term_null_pass and not result.four_point_cancel_pass
    ]

    return {
        "ok": expected_all_observed,
        "samples": samples,
        "seed": seed,
        "dimension": dim,
        "tolerance": tolerance,
        "families": [asdict(result) for result in results],
        "passing_families": passing,
        "failing_families": failing,
        "cross_term_pass_four_point_fail_families": cross_term_pass_four_point_fail,
        "interpretation": {
            "u1a_cross_term_nullity_is_necessary": True,
            "u1a_cross_term_nullity_alone_is_sufficient_for_four_point": False,
            "quadratic_or_modulo_null_linear_cases_pass": all(
                name in passing
                for name in (
                    "quadratic_linear_gluing",
                    "quadratic_linear_with_null_channel",
                    "quadratic_null_residual_gluing",
                )
            ),
            "nonhilbert_energy_counterexamples_detected": all(
                name in failing
                for name in (
                    "l1_squared_linear_gluing",
                    "p3_norm_squared_linear_gluing",
                    "coupled_nonquadratic_linear_gluing",
                )
            ),
        },
        "promotion": {
            "unification_promotion": False,
            "terminal_promotion": False,
            "clay_promotion": False,
        },
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--samples", type=int, default=2000)
    parser.add_argument("--seed", type=int, default=20260609)
    parser.add_argument("--dimension", type=int, default=4)
    parser.add_argument("--tolerance", type=float, default=1.0e-9)
    parser.add_argument("--witness-limit", type=int, default=3)
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
    if args.json:
        print(json.dumps(payload, indent=2, sort_keys=True))
    else:
        print(
            "ok={ok} samples={samples} dim={dimension} passing={passing} failing={failing}".format(
                ok=payload["ok"],
                samples=payload["samples"],
                dimension=payload["dimension"],
                passing=",".join(payload["passing_families"]),
                failing=",".join(payload["failing_families"]),
            )
        )
    return 0 if payload["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
