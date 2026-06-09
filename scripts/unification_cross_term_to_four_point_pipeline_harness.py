#!/usr/bin/env python3
"""Fail-closed diagnostic for the U-1a -> four-point pipeline.

This harness models the unification proof pipeline

    U-1a cross-term nullity
      -> modulo-null linearity
      -> four-point cancellation
      -> parallelogram diagnostics

It is intentionally diagnostic only.  It does not certify any theorem and all
promotion flags remain false.

Families included:
* one good quadratic pipeline;
* multiple bad families where cross-term nullity passes modulo null but the
  downstream four-point/parallelogram layer fails;
* one bad family where the cross-term target itself fails.
"""

from __future__ import annotations

import argparse
import json
import math
import random
import statistics
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Callable, Sequence


Vector = list[float]
Matrix = list[list[float]]
Gluing = Callable[[Vector, Matrix, int], Vector]
Energy = Callable[[Vector], float]

DEFAULT_OUTPUT = Path(
    "outputs/unification_cross_term_to_four_point_pipeline_harness.json"
)


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
            diagonal = 1.0 + 0.05 * (i + 1) if i == j else 0.0
            symmetric = 0.02 * (i + 1) * (j + 2) / max(1, dim)
            alternating = 0.013 * ((-1.0) ** (i + j)) * (1 + abs(i - j))
            row.append(diagonal + symmetric + alternating)
        matrix.append(row)
    return matrix


def representative(rng: random.Random, dim: int) -> Vector:
    q = [rng.uniform(-1.2, 1.2) for _ in range(dim)]
    n = [rng.uniform(-0.8, 0.8) for _ in range(dim)]
    return q + n


def linear_quotient_gluing(x: Vector, matrix: Matrix, dim: int) -> Vector:
    return mat_vec(matrix, quotient(x, dim)) + [0.0] * dim


def null_bilinear_gluing(x: Vector, matrix: Matrix, dim: int) -> Vector:
    q = quotient(x, dim)
    n = null_part(x, dim)
    quotient_out = mat_vec(matrix, q)
    null_out = [
        0.14 * q[i] * q[(i + 1) % dim] + 0.05 * n[i] * n[i] for i in range(dim)
    ]
    return quotient_out + null_out


def nonlinear_quotient_gluing(x: Vector, matrix: Matrix, dim: int) -> Vector:
    q = quotient(x, dim)
    quotient_out = mat_vec(matrix, q)
    if dim >= 1:
        quotient_out[0] += 0.29 * q[0] * q[-1]
    if dim >= 2:
        quotient_out[1] -= 0.17 * q[0] * q[0]
    return quotient_out + [0.0] * dim


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
    return base + 0.2 * coupling


def cross_term(gluing: Gluing, x: Vector, y: Vector, matrix: Matrix, dim: int) -> Vector:
    return sub(
        sub(gluing(add(x, y), matrix, dim), gluing(x, matrix, dim)),
        gluing(y, matrix, dim),
    )


def four_point_residual(
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


def parallelogram_residual(
    gluing: Gluing,
    energy: Energy,
    x: Vector,
    y: Vector,
    matrix: Matrix,
    dim: int,
) -> float:
    return four_point_residual(gluing, energy, x, y, matrix, dim)


def two_homogeneity_error(
    gluing: Gluing,
    energy: Energy,
    x: Vector,
    matrix: Matrix,
    dim: int,
) -> float:
    return abs(energy(gluing(scale(2.0, x), matrix, dim)) - 4.0 * energy(gluing(x, matrix, dim)))


@dataclass(frozen=True)
class Family:
    name: str
    expected: str
    gluing: Gluing
    energy: Energy
    should_cross_term_be_null: bool
    should_four_point_cancel: bool


@dataclass(frozen=True)
class FamilyMetrics:
    name: str
    expected: str
    cross_term_null_pass: bool
    modulo_null_linearity_pass: bool
    four_point_cancel_pass: bool
    parallelogram_pass: bool
    two_homogeneous_pass: bool
    expected_outcome_observed: bool
    mean_modulo_null_residual: float
    max_modulo_null_residual: float
    mean_abs_four_point_residual: float
    max_abs_four_point_residual: float
    mean_abs_parallelogram_residual: float
    max_abs_parallelogram_residual: float
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


def evaluate_family(
    family: Family,
    xs: Sequence[Vector],
    ys: Sequence[Vector],
    matrix: Matrix,
    dim: int,
    tolerance: float,
    witness_limit: int,
) -> FamilyMetrics:
    modulo_null_residuals: list[float] = []
    four_point_residuals: list[float] = []
    parallelogram_residuals: list[float] = []
    homogeneity_errors: list[float] = []
    witnesses: list[dict[str, object]] = []

    for index, (x, y) in enumerate(zip(xs, ys)):
        c = cross_term(family.gluing, x, y, matrix, dim)
        mod_residual = l2_norm(quotient(c, dim))
        four_point = abs(four_point_residual(family.gluing, family.energy, x, y, matrix, dim))
        parallelogram = abs(parallelogram_residual(family.gluing, family.energy, x, y, matrix, dim))
        hom_error = two_homogeneity_error(family.gluing, family.energy, x, matrix, dim)
        combined = mod_residual + four_point + hom_error

        modulo_null_residuals.append(mod_residual)
        four_point_residuals.append(four_point)
        parallelogram_residuals.append(parallelogram)
        homogeneity_errors.append(hom_error)

        if combined > tolerance:
            witnesses.append(
                {
                    "sample": index,
                    "combined_error": combined,
                    "cross_term_mod_null_residual": mod_residual,
                    "four_point_residual": four_point,
                    "parallelogram_residual": parallelogram,
                    "two_homogeneity_error": hom_error,
                    "quotient_x": quotient(x, dim),
                    "quotient_y": quotient(y, dim),
                    "cross_term_quotient": quotient(c, dim),
                    "cross_term_null": null_part(c, dim),
                }
            )
            witnesses.sort(key=lambda item: float(item["combined_error"]), reverse=True)
            del witnesses[witness_limit:]

    cross_term_null_pass = max(modulo_null_residuals, default=0.0) <= tolerance
    modulo_null_linearity_pass = cross_term_null_pass
    four_point_cancel_pass = max(four_point_residuals, default=0.0) <= tolerance
    parallelogram_pass = max(parallelogram_residuals, default=0.0) <= tolerance
    two_homogeneous_pass = max(homogeneity_errors, default=0.0) <= tolerance

    failed_checks: list[str] = []
    if not cross_term_null_pass:
        failed_checks.append("cross_term_not_null_modulo_null_class")
    if not two_homogeneous_pass:
        failed_checks.append("energy_not_two_homogeneous")
    if not four_point_cancel_pass:
        failed_checks.append("four_point_defect_nonzero")
    if not parallelogram_pass:
        failed_checks.append("parallelogram_defect_nonzero")

    expected_outcome_observed = (
        cross_term_null_pass == family.should_cross_term_be_null
        and four_point_cancel_pass == family.should_four_point_cancel
    )

    return FamilyMetrics(
        name=family.name,
        expected=family.expected,
        cross_term_null_pass=cross_term_null_pass,
        modulo_null_linearity_pass=modulo_null_linearity_pass,
        four_point_cancel_pass=four_point_cancel_pass,
        parallelogram_pass=parallelogram_pass,
        two_homogeneous_pass=two_homogeneous_pass,
        expected_outcome_observed=expected_outcome_observed,
        mean_modulo_null_residual=statistics.fmean(modulo_null_residuals)
        if modulo_null_residuals
        else 0.0,
        max_modulo_null_residual=max(modulo_null_residuals) if modulo_null_residuals else 0.0,
        mean_abs_four_point_residual=statistics.fmean(four_point_residuals)
        if four_point_residuals
        else 0.0,
        max_abs_four_point_residual=max(four_point_residuals) if four_point_residuals else 0.0,
        mean_abs_parallelogram_residual=statistics.fmean(parallelogram_residuals)
        if parallelogram_residuals
        else 0.0,
        max_abs_parallelogram_residual=max(parallelogram_residuals)
        if parallelogram_residuals
        else 0.0,
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
            name="good_quadratic_pipeline",
            expected="good: cross-term nullity and four-point/parallelogram both pass",
            gluing=linear_quotient_gluing,
            energy=quotient_quadratic,
            should_cross_term_be_null=True,
            should_four_point_cancel=True,
        ),
        Family(
            name="bad_l1_squared_downstream",
            expected="bad downstream: cross-term passes, four-point/parallelogram fail",
            gluing=linear_quotient_gluing,
            energy=l1_squared_energy,
            should_cross_term_be_null=True,
            should_four_point_cancel=False,
        ),
        Family(
            name="bad_p3_norm_squared_downstream",
            expected="bad downstream: cross-term passes, four-point/parallelogram fail",
            gluing=linear_quotient_gluing,
            energy=p3_norm_squared_energy,
            should_cross_term_be_null=True,
            should_four_point_cancel=False,
        ),
        Family(
            name="bad_coupled_nonquadratic_downstream",
            expected="bad downstream: cross-term passes, four-point/parallelogram fail",
            gluing=linear_quotient_gluing,
            energy=coupled_nonquadratic_energy,
            should_cross_term_be_null=True,
            should_four_point_cancel=False,
        ),
        Family(
            name="good_modulo_null_bilinear_pipeline",
            expected="good modulo null: nonlinear null-only channel still passes quotient quadratic diagnostics",
            gluing=null_bilinear_gluing,
            energy=quotient_quadratic,
            should_cross_term_be_null=True,
            should_four_point_cancel=True,
        ),
        Family(
            name="bad_cross_term_failure",
            expected="bad U-1a: cross-term already leaks into the quotient",
            gluing=nonlinear_quotient_gluing,
            energy=quotient_quadratic,
            should_cross_term_be_null=False,
            should_four_point_cancel=False,
        ),
    ]


def run(samples: int, seed: int, dim: int, tolerance: float, witness_limit: int) -> dict[str, Any]:
    rng = random.Random(seed)
    xs = [representative(rng, dim) for _ in range(samples)]
    ys = [representative(rng, dim) for _ in range(samples)]
    matrix = deterministic_matrix(dim)
    families = build_families(dim)
    results = [
        evaluate_family(family, xs, ys, matrix, dim, tolerance, witness_limit)
        for family in families
    ]

    family_rows = [asdict(result) for result in results]
    good_families = [result.name for result in results if not result.failed_checks]
    downstream_counterexamples = [
        result.name
        for result in results
        if result.cross_term_null_pass and not result.four_point_cancel_pass
    ]
    direct_cross_term_failures = [
        result.name for result in results if not result.cross_term_null_pass
    ]
    expected_all_observed = all(result.expected_outcome_observed for result in results)

    return {
        "ok": expected_all_observed,
        "samples": samples,
        "seed": seed,
        "dimension": dim,
        "tolerance": tolerance,
        "families": family_rows,
        "good_families": good_families,
        "downstream_counterexample_families": downstream_counterexamples,
        "direct_cross_term_failure_families": direct_cross_term_failures,
        "pipeline_summary": {
            "u1a_cross_term_nullity_is_necessary": True,
            "modulo_null_linearity_is_modeled_by_quotient_residual": True,
            "cross_term_nullity_alone_implies_four_point": False,
            "cross_term_nullity_alone_implies_parallelogram": False,
            "good_quadratic_pipeline_passes": "good_quadratic_pipeline" in good_families,
            "good_modulo_null_pipeline_passes": "good_modulo_null_bilinear_pipeline" in good_families,
            "multiple_downstream_counterexamples_detected": len(downstream_counterexamples) >= 3,
            "direct_cross_term_failure_detected": len(direct_cross_term_failures) >= 1,
        },
        "promotion": {
            "unification_promotion": False,
            "clay_promotion": False,
            "terminal_promotion": False,
        },
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--samples", type=int, default=2000)
    parser.add_argument("--seed", type=int, default=20260609)
    parser.add_argument("--dimension", type=int, default=4)
    parser.add_argument("--tolerance", type=float, default=1.0e-9)
    parser.add_argument("--witness-limit", type=int, default=3)
    parser.add_argument("--quick", action="store_true")
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--json-output", type=Path, default=DEFAULT_OUTPUT)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    samples = min(args.samples, 256) if args.quick else args.samples
    if samples <= 0:
        raise SystemExit("--samples must be positive")
    if args.dimension <= 1:
        raise SystemExit("--dimension must be at least 2")
    if args.witness_limit < 0:
        raise SystemExit("--witness-limit must be nonnegative")

    payload = run(
        samples=samples,
        seed=args.seed,
        dim=args.dimension,
        tolerance=args.tolerance,
        witness_limit=args.witness_limit,
    )

    if args.json_output:
        args.json_output.parent.mkdir(parents=True, exist_ok=True)
        args.json_output.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")

    if args.json:
        print(json.dumps(payload, indent=2, sort_keys=True))
    else:
        print(
            "ok={ok} good={good} downstream_bad={downstream_bad} cross_term_bad={cross_bad}".format(
                ok=payload["ok"],
                good=",".join(payload["good_families"]),
                downstream_bad=",".join(payload["downstream_counterexample_families"]),
                cross_bad=",".join(payload["direct_cross_term_failure_families"]),
            )
        )

    return 0 if payload["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
