#!/usr/bin/env python3
"""Sharper finite diagnostic for modulo-null gluing linearity.

This harness isolates four quotient-sensitive checks that sit between the broad
U-1a cross-term target and the downstream four-point/parallelogram layer:

1. representative invariance:
     changing only the null representative should not change the quotient class
2. null-class transport:
     null perturbations should stay null after gluing
3. quotient equality:
     equal quotient classes should glue to equal quotient outputs
4. modulo-null gluing linearity:
     G(x + y) - G(x) - G(y) should lie entirely in the null class

The families are intentionally narrower than the existing broad cross-term
harness. Good families satisfy all four quotient-level requirements; bad
families each fail for one concrete reason:

* representative-dependent quotient leakage
* null-to-quotient transport leakage
* nonlinear quotient response
* quotient-class dependent representative choice

Diagnostic only. Promotion remains false.
"""

from __future__ import annotations

import argparse
import json
import math
import random
import statistics
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Callable, Sequence


Vector = list[float]
Matrix = list[list[float]]
Gluing = Callable[[Vector, Matrix, int], Vector]


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


def assemble(q: Sequence[float], n: Sequence[float]) -> Vector:
    return list(q) + list(n)


def mat_vec(matrix: Matrix, vector: Sequence[float]) -> Vector:
    return [dot(row, vector) for row in matrix]


def deterministic_matrix(dim: int) -> Matrix:
    matrix: Matrix = []
    for i in range(dim):
        row: Vector = []
        for j in range(dim):
            diagonal = 1.0 + 0.08 * (i + 1) if i == j else 0.0
            symmetric = 0.021 * (i + 2) * (j + 1) / max(1, dim)
            alternating = 0.009 * ((-1.0) ** (i + j)) * (1 + abs(i - j))
            row.append(diagonal + symmetric + alternating)
        matrix.append(row)
    return matrix


def representative(rng: random.Random, dim: int) -> Vector:
    q = [rng.uniform(-1.25, 1.25) for _ in range(dim)]
    n = [rng.uniform(-0.85, 0.85) for _ in range(dim)]
    return assemble(q, n)


def representative_shift(rng: random.Random, dim: int, magnitude: float) -> Vector:
    return [0.0] * dim + [rng.uniform(-magnitude, magnitude) for _ in range(dim)]


def linear_quotient_gluing(x: Vector, matrix: Matrix, dim: int) -> Vector:
    return assemble(mat_vec(matrix, quotient(x, dim)), [0.0] * dim)


def affine_null_channel_gluing(x: Vector, matrix: Matrix, dim: int) -> Vector:
    q = quotient(x, dim)
    n = null_part(x, dim)
    quotient_out = mat_vec(matrix, q)
    null_out = [0.22 * q[i] - 0.14 * n[i] for i in range(dim)]
    return assemble(quotient_out, null_out)


def quadratic_null_only_gluing(x: Vector, matrix: Matrix, dim: int) -> Vector:
    q = quotient(x, dim)
    n = null_part(x, dim)
    quotient_out = mat_vec(matrix, q)
    null_out: Vector = []
    for i in range(dim):
        left = q[i]
        right = q[(i + 1) % dim]
        null_out.append(0.17 * left * right + 0.05 * n[i] * n[i])
    return assemble(quotient_out, null_out)


def representative_dependent_quotient_gluing(x: Vector, matrix: Matrix, dim: int) -> Vector:
    q = quotient(x, dim)
    n = null_part(x, dim)
    quotient_out = mat_vec(matrix, q)
    if quotient_out:
        quotient_out[0] += 0.33 * n[0]
    if len(quotient_out) > 1:
        quotient_out[1] -= 0.18 * n[-1]
    return assemble(quotient_out, [0.0] * dim)


def null_transport_leak_gluing(x: Vector, matrix: Matrix, dim: int) -> Vector:
    q = quotient(x, dim)
    n = null_part(x, dim)
    quotient_out = mat_vec(matrix, q)
    leak = sum(n) / max(1, dim)
    quotient_out = [value + 0.12 * leak for value in quotient_out]
    return assemble(quotient_out, [0.11 * n[i] for i in range(dim)])


def nonlinear_quotient_gluing(x: Vector, matrix: Matrix, dim: int) -> Vector:
    q = quotient(x, dim)
    quotient_out = mat_vec(matrix, q)
    if quotient_out:
        quotient_out[0] += 0.29 * q[0] * q[-1]
    if len(quotient_out) > 1:
        quotient_out[1] -= 0.16 * q[0] * q[0]
    return assemble(quotient_out, [0.0] * dim)


def quotient_class_split_gluing(x: Vector, matrix: Matrix, dim: int) -> Vector:
    q = quotient(x, dim)
    n = null_part(x, dim)
    quotient_out = mat_vec(matrix, q)
    marker = 1.0 if sum(value * value for value in n) > 0.25 * dim else -1.0
    quotient_out = [value + 0.09 * marker for value in quotient_out]
    return assemble(quotient_out, [0.07 * n[i] for i in range(dim)])


@dataclass(frozen=True)
class Family:
    name: str
    expected: str
    gluing: Gluing
    should_rep_invariant: bool
    should_null_transport: bool
    should_quotient_equal: bool
    should_modulo_linear: bool


@dataclass(frozen=True)
class SampleRow:
    representative_invariance_residual: float
    null_transport_residual: float
    quotient_equality_residual: float
    modulo_null_linearity_residual: float
    total_residual: float


@dataclass(frozen=True)
class FamilyMetrics:
    name: str
    expected: str
    expected_outcome_observed: bool
    representative_invariance_pass: bool
    null_transport_pass: bool
    quotient_equality_pass: bool
    modulo_null_linearity_pass: bool
    mean_representative_invariance_residual: float
    max_representative_invariance_residual: float
    mean_null_transport_residual: float
    max_null_transport_residual: float
    mean_quotient_equality_residual: float
    max_quotient_equality_residual: float
    mean_modulo_null_linearity_residual: float
    max_modulo_null_linearity_residual: float
    failed_checks: list[str]
    witness_count: int
    worst_witnesses: list[dict[str, object]]


def percentile(values: Sequence[float], q: float) -> float:
    if not values:
        return 0.0
    ordered = sorted(values)
    index = min(len(ordered) - 1, max(0, math.ceil(q * len(ordered)) - 1))
    return ordered[index]


def representative_invariance_residual(
    gluing: Gluing,
    x: Vector,
    null_shift: Vector,
    matrix: Matrix,
    dim: int,
) -> float:
    base = quotient(gluing(x, matrix, dim), dim)
    shifted = quotient(gluing(add(x, null_shift), matrix, dim), dim)
    return l2_norm(sub(base, shifted))


def null_transport_residual(
    gluing: Gluing,
    null_shift: Vector,
    matrix: Matrix,
    dim: int,
) -> float:
    return l2_norm(quotient(gluing(null_shift, matrix, dim), dim))


def quotient_equality_residual(
    gluing: Gluing,
    q: Vector,
    rep_a_null: Vector,
    rep_b_null: Vector,
    matrix: Matrix,
    dim: int,
) -> float:
    rep_a = assemble(q, rep_a_null)
    rep_b = assemble(q, rep_b_null)
    image_a = quotient(gluing(rep_a, matrix, dim), dim)
    image_b = quotient(gluing(rep_b, matrix, dim), dim)
    return l2_norm(sub(image_a, image_b))


def modulo_null_linearity_residual(
    gluing: Gluing,
    x: Vector,
    y: Vector,
    matrix: Matrix,
    dim: int,
) -> float:
    cross = sub(
        sub(gluing(add(x, y), matrix, dim), gluing(x, matrix, dim)),
        gluing(y, matrix, dim),
    )
    return l2_norm(quotient(cross, dim))


def evaluate_family(
    family: Family,
    xs: Sequence[Vector],
    ys: Sequence[Vector],
    shifts_a: Sequence[Vector],
    shifts_b: Sequence[Vector],
    matrix: Matrix,
    dim: int,
    tolerance: float,
    witness_limit: int,
) -> FamilyMetrics:
    rows: list[SampleRow] = []
    witnesses: list[dict[str, object]] = []

    for index, (x, y, shift_a, shift_b) in enumerate(zip(xs, ys, shifts_a, shifts_b)):
        q = quotient(x, dim)
        rep_res = representative_invariance_residual(family.gluing, x, shift_a, matrix, dim)
        transport_res = null_transport_residual(family.gluing, shift_a, matrix, dim)
        equality_res = quotient_equality_residual(
            family.gluing,
            q,
            null_part(x, dim),
            null_part(add(x, shift_b), dim),
            matrix,
            dim,
        )
        mod_linear_res = modulo_null_linearity_residual(family.gluing, x, y, matrix, dim)
        total = rep_res + transport_res + equality_res + mod_linear_res
        row = SampleRow(
            representative_invariance_residual=rep_res,
            null_transport_residual=transport_res,
            quotient_equality_residual=equality_res,
            modulo_null_linearity_residual=mod_linear_res,
            total_residual=total,
        )
        rows.append(row)
        if total > tolerance:
            witnesses.append(
                {
                    "sample": index,
                    **asdict(row),
                    "quotient_x": quotient(x, dim),
                    "null_x": null_part(x, dim),
                    "quotient_y": quotient(y, dim),
                    "null_y": null_part(y, dim),
                    "shift_a_null": null_part(shift_a, dim),
                    "shift_b_null": null_part(shift_b, dim),
                }
            )
            witnesses.sort(key=lambda item: float(item["total_residual"]), reverse=True)
            del witnesses[witness_limit:]

    rep_residuals = [row.representative_invariance_residual for row in rows]
    transport_residuals = [row.null_transport_residual for row in rows]
    equality_residuals = [row.quotient_equality_residual for row in rows]
    mod_linear_residuals = [row.modulo_null_linearity_residual for row in rows]

    representative_invariance_pass = max(rep_residuals, default=0.0) <= tolerance
    null_transport_pass = max(transport_residuals, default=0.0) <= tolerance
    quotient_equality_pass = max(equality_residuals, default=0.0) <= tolerance
    modulo_null_linearity_pass = max(mod_linear_residuals, default=0.0) <= tolerance

    expected_outcome_observed = (
        representative_invariance_pass == family.should_rep_invariant
        and null_transport_pass == family.should_null_transport
        and quotient_equality_pass == family.should_quotient_equal
        and modulo_null_linearity_pass == family.should_modulo_linear
    )

    failed_checks: list[str] = []
    if not representative_invariance_pass:
        failed_checks.append("representative_invariance_failed")
    if not null_transport_pass:
        failed_checks.append("null_transport_failed")
    if not quotient_equality_pass:
        failed_checks.append("quotient_equality_failed")
    if not modulo_null_linearity_pass:
        failed_checks.append("modulo_null_linearity_failed")

    return FamilyMetrics(
        name=family.name,
        expected=family.expected,
        expected_outcome_observed=expected_outcome_observed,
        representative_invariance_pass=representative_invariance_pass,
        null_transport_pass=null_transport_pass,
        quotient_equality_pass=quotient_equality_pass,
        modulo_null_linearity_pass=modulo_null_linearity_pass,
        mean_representative_invariance_residual=statistics.fmean(rep_residuals) if rep_residuals else 0.0,
        max_representative_invariance_residual=max(rep_residuals) if rep_residuals else 0.0,
        mean_null_transport_residual=statistics.fmean(transport_residuals) if transport_residuals else 0.0,
        max_null_transport_residual=max(transport_residuals) if transport_residuals else 0.0,
        mean_quotient_equality_residual=statistics.fmean(equality_residuals) if equality_residuals else 0.0,
        max_quotient_equality_residual=max(equality_residuals) if equality_residuals else 0.0,
        mean_modulo_null_linearity_residual=statistics.fmean(mod_linear_residuals)
        if mod_linear_residuals
        else 0.0,
        max_modulo_null_linearity_residual=max(mod_linear_residuals) if mod_linear_residuals else 0.0,
        failed_checks=failed_checks,
        witness_count=len(witnesses),
        worst_witnesses=witnesses,
    )


def build_families() -> list[Family]:
    return [
        Family(
            name="linear_quotient_gluing",
            expected="pass: quotient-only linear gluing is rep-invariant, null-transport safe, quotient-equal, and modulo-null linear",
            gluing=linear_quotient_gluing,
            should_rep_invariant=True,
            should_null_transport=True,
            should_quotient_equal=True,
            should_modulo_linear=True,
        ),
        Family(
            name="affine_null_channel_gluing",
            expected="pass: null output may vary, but quotient class is linear and representative-invariant",
            gluing=affine_null_channel_gluing,
            should_rep_invariant=True,
            should_null_transport=True,
            should_quotient_equal=True,
            should_modulo_linear=True,
        ),
        Family(
            name="quadratic_null_only_gluing",
            expected="pass modulo null: quotient class stays linear while null channel is nonlinear",
            gluing=quadratic_null_only_gluing,
            should_rep_invariant=True,
            should_null_transport=True,
            should_quotient_equal=True,
            should_modulo_linear=True,
        ),
        Family(
            name="representative_dependent_quotient_gluing",
            expected="fail: quotient output depends on null representative",
            gluing=representative_dependent_quotient_gluing,
            should_rep_invariant=False,
            should_null_transport=False,
            should_quotient_equal=False,
            should_modulo_linear=True,
        ),
        Family(
            name="null_transport_leak_gluing",
            expected="fail: pure null inputs leak into quotient output",
            gluing=null_transport_leak_gluing,
            should_rep_invariant=False,
            should_null_transport=False,
            should_quotient_equal=False,
            should_modulo_linear=True,
        ),
        Family(
            name="nonlinear_quotient_gluing",
            expected="fail: quotient nonlinearity breaks modulo-null linearity",
            gluing=nonlinear_quotient_gluing,
            should_rep_invariant=True,
            should_null_transport=True,
            should_quotient_equal=True,
            should_modulo_linear=False,
        ),
        Family(
            name="quotient_class_split_gluing",
            expected="fail: same quotient class can split by representative bucket",
            gluing=quotient_class_split_gluing,
            should_rep_invariant=False,
            should_null_transport=False,
            should_quotient_equal=False,
            should_modulo_linear=False,
        ),
    ]


def run(samples: int, seed: int, dim: int, tolerance: float, witness_limit: int) -> dict[str, object]:
    rng = random.Random(seed)
    matrix = deterministic_matrix(dim)
    xs = [representative(rng, dim) for _ in range(samples)]
    ys = [representative(rng, dim) for _ in range(samples)]
    shifts_a = [representative_shift(rng, dim, 0.75) for _ in range(samples)]
    shifts_b = [representative_shift(rng, dim, 0.95) for _ in range(samples)]

    families = build_families()
    results = [
        evaluate_family(family, xs, ys, shifts_a, shifts_b, matrix, dim, tolerance, witness_limit)
        for family in families
    ]

    passing_rep_invariant = [
        result.name for result in results if result.representative_invariance_pass
    ]
    failing_rep_dependent = [
        result.name for result in results if not result.representative_invariance_pass
    ]
    passing_modulo_linear = [
        result.name for result in results if result.modulo_null_linearity_pass
    ]
    failing_modulo_linear = [
        result.name for result in results if not result.modulo_null_linearity_pass
    ]

    return {
        "ok": all(result.expected_outcome_observed for result in results),
        "harness": "unification_modulo_null_linearity_harness",
        "scope": "finite_quotient_nullclass_diagnostic",
        "samples": samples,
        "seed": seed,
        "dimension": dim,
        "tolerance": tolerance,
        "families": [asdict(result) for result in results],
        "passing_representative_invariant_families": passing_rep_invariant,
        "failing_representative_dependent_families": failing_rep_dependent,
        "passing_modulo_null_linear_families": passing_modulo_linear,
        "failing_modulo_null_linear_families": failing_modulo_linear,
        "summary": {
            "good_cases_all_pass": all(
                family_name in passing_modulo_linear and family_name in passing_rep_invariant
                for family_name in (
                    "linear_quotient_gluing",
                    "affine_null_channel_gluing",
                    "quadratic_null_only_gluing",
                )
            ),
            "bad_representative_dependent_cases_detected": all(
                family_name in failing_rep_dependent
                for family_name in (
                    "representative_dependent_quotient_gluing",
                    "null_transport_leak_gluing",
                    "quotient_class_split_gluing",
                )
            ),
            "bad_modulo_null_linearity_case_detected": "nonlinear_quotient_gluing"
            in failing_modulo_linear,
            "null_transport_is_stricter_than_cross_term_alone": True,
            "quotient_equality_requires_representative_invariance": True,
            "p95_modulo_null_linearity_residual": percentile(
                [result.max_modulo_null_linearity_residual for result in results], 0.95
            ),
        },
        "promotion": {
            "u1a_proved": False,
            "unification_promoted": False,
            "clay_promoted": False,
            "terminal": False,
        },
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--samples", type=int, default=2400)
    parser.add_argument("--seed", type=int, default=20260609)
    parser.add_argument("--dimension", type=int, default=4)
    parser.add_argument("--tolerance", type=float, default=1.0e-9)
    parser.add_argument("--witness-limit", type=int, default=3)
    parser.add_argument("--quick", action="store_true")
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--json-output", type=Path)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    if args.samples <= 0:
        raise SystemExit("--samples must be positive")
    if args.dimension <= 1:
        raise SystemExit("--dimension must be at least 2")
    if args.witness_limit < 0:
        raise SystemExit("--witness-limit must be nonnegative")

    samples = min(args.samples, 600) if args.quick else args.samples
    payload = run(
        samples=samples,
        seed=args.seed,
        dim=args.dimension,
        tolerance=args.tolerance,
        witness_limit=args.witness_limit,
    )

    text = json.dumps(payload, indent=2 if args.json else None, sort_keys=True)
    if args.json_output is not None:
        args.json_output.parent.mkdir(parents=True, exist_ok=True)
        args.json_output.write_text(json.dumps(payload, sort_keys=True) + "\n", encoding="utf-8")

    if args.json:
        print(text)
    else:
        print(
            "ok={ok} samples={samples} dim={dimension} rep_pass={rep_pass} mod_linear_fail={mod_fail}".format(
                ok=payload["ok"],
                samples=payload["samples"],
                dimension=payload["dimension"],
                rep_pass=",".join(payload["passing_representative_invariant_families"]),
                mod_fail=",".join(payload["failing_modulo_null_linear_families"]),
            )
        )
    return 0 if payload["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
