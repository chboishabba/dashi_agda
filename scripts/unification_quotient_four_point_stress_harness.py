#!/usr/bin/env python3
"""Stress diagnostic for quotient four-point residuals.

This pure-stdlib harness models a finite representative space
R^(2d) = quotient coordinates R^d plus null/gauge coordinates R^d.  It
checks whether a gluing/energy proxy is:

  * invariant under representative shifts in the null coordinates;
  * additive and scalar-compatible on quotient representatives;
  * two-homogeneous at the energy level;
  * four-point/parallelogram cancelling.

The good case is a representative-invariant linear quotient map with a
quadratic energy.  The bad cases are deliberately finite counterprofiles:
representative-shift leakage, nonlinear quotient gluing, a p-norm
two-homogeneous near miss, and an asymmetric cross-term.  This is a diagnostic
only and always emits promotion=false.
"""

from __future__ import annotations

import argparse
import json
import math
import random
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Callable, Sequence


Vector = list[float]
Matrix = list[list[float]]
Gluing = Callable[[Vector, Matrix, int], Vector]
Energy = Callable[[Vector, Matrix, int, Gluing], float]

DEFAULT_JSON_OUTPUT = Path("outputs/unification_quotient_four_point_stress.json")
SEED = 20260608


def add(x: Sequence[float], y: Sequence[float]) -> Vector:
    return [a + b for a, b in zip(x, y)]


def sub(x: Sequence[float], y: Sequence[float]) -> Vector:
    return [a - b for a, b in zip(x, y)]


def scale(alpha: float, x: Sequence[float]) -> Vector:
    return [alpha * value for value in x]


def dot(x: Sequence[float], y: Sequence[float]) -> float:
    return sum(a * b for a, b in zip(x, y))


def norm2(x: Sequence[float]) -> float:
    return math.sqrt(max(0.0, dot(x, x)))


def quotient(x: Sequence[float], dimension: int) -> Vector:
    return list(x[:dimension])


def null_part(x: Sequence[float], dimension: int) -> Vector:
    return list(x[dimension:])


def mat_vec(matrix: Matrix, vector: Sequence[float]) -> Vector:
    return [dot(row, vector) for row in matrix]


def deterministic_matrix(dimension: int) -> Matrix:
    """Stable mixed matrix with positive diagonal and nontrivial couplings."""
    matrix: Matrix = []
    for i in range(dimension):
        row: Vector = []
        for j in range(dimension):
            diagonal = 1.0 + 0.09 * (i + 1) if i == j else 0.0
            symmetric = 0.031 * (i + 1) * (j + 1) / max(1, dimension)
            alternating = 0.017 * ((-1.0) ** (i + j)) * (1 + abs(i - j))
            row.append(diagonal + symmetric + alternating)
        matrix.append(row)
    return matrix


def representative(rng: random.Random, dimension: int) -> Vector:
    q = [rng.uniform(-1.4, 1.4) for _ in range(dimension)]
    n = [rng.uniform(-1.0, 1.0) for _ in range(dimension)]
    return q + n


def null_shift(rng: random.Random, dimension: int) -> Vector:
    return [0.0] * dimension + [rng.uniform(-1.2, 1.2) for _ in range(dimension)]


def linear_quotient_gluing(x: Vector, matrix: Matrix, dimension: int) -> Vector:
    return mat_vec(matrix, quotient(x, dimension))


def representative_shift_leak_gluing(x: Vector, matrix: Matrix, dimension: int) -> Vector:
    out = linear_quotient_gluing(x, matrix, dimension)
    null = null_part(x, dimension)
    if out:
        out[0] += 0.39 * sum((i + 1) * value for i, value in enumerate(null))
    if len(out) > 1:
        out[1] -= 0.23 * sum(value * value for value in null)
    return out


def nonlinear_quotient_gluing(x: Vector, matrix: Matrix, dimension: int) -> Vector:
    q = quotient(x, dimension)
    out = linear_quotient_gluing(x, matrix, dimension)
    if out:
        out[0] += 0.24 * q[0] * q[-1]
    if len(out) > 1:
        out[1] -= 0.18 * q[0] * q[0]
    if len(out) > 2:
        out[2] += 0.13 * sum(value * value for value in q)
    return out


def p_norm_near_miss_gluing(x: Vector, matrix: Matrix, dimension: int) -> Vector:
    return linear_quotient_gluing(x, matrix, dimension)


def asymmetric_cross_term_gluing(x: Vector, matrix: Matrix, dimension: int) -> Vector:
    q = quotient(x, dimension)
    out = linear_quotient_gluing(x, matrix, dimension)
    if len(out) > 1:
        out[0] += 0.21 * q[0] * q[1]
        out[1] -= 0.09 * q[1] * max(q[0], 0.0)
    elif out:
        out[0] += 0.21 * q[0] * q[0]
    return out


def quadratic_energy(x: Vector, matrix: Matrix, dimension: int, gluing: Gluing) -> float:
    gx = gluing(x, matrix, dimension)
    return dot(gx, gx)


def p_norm_two_homogeneous_energy(
    x: Vector, matrix: Matrix, dimension: int, gluing: Gluing
) -> float:
    gx = gluing(x, matrix, dimension)
    p = 3.0
    total = sum(abs(value) ** p for value in gx)
    return total ** (2.0 / p)


@dataclass(frozen=True)
class CaseSpec:
    name: str
    kind: str
    expected: str
    gluing: Gluing
    energy: Energy


@dataclass(frozen=True)
class Row:
    sample: int
    case: str
    representative_shift_error: float
    additivity_error: float
    scalar_compatibility_error: float
    energy_two_homogeneity_error: float
    four_point_residual_error: float
    combined_error: float


@dataclass(frozen=True)
class CaseMetrics:
    name: str
    kind: str
    expected: str
    observed_pass: bool
    expected_outcome_observed: bool
    representative_invariant: bool
    additive: bool
    scalar_compatible: bool
    energy_two_homogeneous: bool
    four_point_residual_zero: bool
    failed_checks: list[str]
    max_errors: dict[str, float]
    mean_errors: dict[str, float]
    p95_errors: dict[str, float]
    witness_count: int
    worst_witnesses: list[dict[str, object]]


def percentile(values: Sequence[float], q: float) -> float:
    if not values:
        return 0.0
    ordered = sorted(values)
    index = min(len(ordered) - 1, max(0, int(math.ceil(q * len(ordered)) - 1)))
    return ordered[index]


def four_point_residual(
    energy: Energy,
    gluing: Gluing,
    x: Vector,
    y: Vector,
    matrix: Matrix,
    dimension: int,
) -> float:
    return (
        energy(add(x, y), matrix, dimension, gluing)
        + energy(sub(x, y), matrix, dimension, gluing)
        - 2.0 * energy(x, matrix, dimension, gluing)
        - 2.0 * energy(y, matrix, dimension, gluing)
    )


def append_witness(
    witnesses: list[dict[str, object]], row: Row, x: Vector, y: Vector, shift: Vector, limit: int
) -> None:
    witnesses.append(
        {
            **asdict(row),
            "quotient_x": quotient(x, len(x) // 2),
            "quotient_y": quotient(y, len(y) // 2),
            "null_shift": null_part(shift, len(shift) // 2),
        }
    )
    witnesses.sort(key=lambda item: float(item["combined_error"]), reverse=True)
    del witnesses[limit:]


def run_case(
    spec: CaseSpec,
    xs: Sequence[Vector],
    ys: Sequence[Vector],
    shifts: Sequence[Vector],
    alphas: Sequence[float],
    matrix: Matrix,
    dimension: int,
    tolerance: float,
    witness_limit: int,
) -> tuple[CaseMetrics, list[Row]]:
    buckets: dict[str, list[float]] = {
        "representative_shift": [],
        "additivity": [],
        "scalar_compatibility": [],
        "energy_two_homogeneity": [],
        "four_point_residual": [],
    }
    rows: list[Row] = []
    witnesses: list[dict[str, object]] = []

    for sample, x in enumerate(xs):
        y = ys[sample]
        shift = shifts[sample]
        alpha = alphas[sample]
        gx = spec.gluing(x, matrix, dimension)
        gy = spec.gluing(y, matrix, dimension)

        rep_error = norm2(sub(spec.gluing(add(x, shift), matrix, dimension), gx))
        add_error = norm2(sub(spec.gluing(add(x, y), matrix, dimension), add(gx, gy)))
        scalar_error = norm2(
            sub(spec.gluing(scale(alpha, x), matrix, dimension), scale(alpha, gx))
        )
        lhs_hom = spec.energy(scale(alpha, x), matrix, dimension, spec.gluing)
        rhs_hom = alpha * alpha * spec.energy(x, matrix, dimension, spec.gluing)
        hom_error = abs(lhs_hom - rhs_hom)
        fp_error = abs(
            four_point_residual(spec.energy, spec.gluing, x, y, matrix, dimension)
        )
        row = Row(
            sample=sample,
            case=spec.name,
            representative_shift_error=rep_error,
            additivity_error=add_error,
            scalar_compatibility_error=scalar_error,
            energy_two_homogeneity_error=hom_error,
            four_point_residual_error=fp_error,
            combined_error=max(rep_error, add_error, scalar_error, hom_error, fp_error),
        )
        rows.append(row)
        buckets["representative_shift"].append(rep_error)
        buckets["additivity"].append(add_error)
        buckets["scalar_compatibility"].append(scalar_error)
        buckets["energy_two_homogeneity"].append(hom_error)
        buckets["four_point_residual"].append(fp_error)
        if row.combined_error > tolerance or len(witnesses) < witness_limit:
            append_witness(witnesses, row, x, y, shift, witness_limit)

    max_errors = {name: max(values, default=0.0) for name, values in buckets.items()}
    mean_errors = {
        name: (sum(values) / len(values) if values else 0.0)
        for name, values in buckets.items()
    }
    p95_errors = {name: percentile(values, 0.95) for name, values in buckets.items()}
    checks = {name: value <= tolerance for name, value in max_errors.items()}
    observed_pass = all(checks.values())
    expected_outcome_observed = observed_pass if spec.kind == "good" else not observed_pass
    failed_checks = [name for name, passed in checks.items() if not passed]

    return (
        CaseMetrics(
            name=spec.name,
            kind=spec.kind,
            expected=spec.expected,
            observed_pass=observed_pass,
            expected_outcome_observed=expected_outcome_observed,
            representative_invariant=checks["representative_shift"],
            additive=checks["additivity"],
            scalar_compatible=checks["scalar_compatibility"],
            energy_two_homogeneous=checks["energy_two_homogeneity"],
            four_point_residual_zero=checks["four_point_residual"],
            failed_checks=failed_checks,
            max_errors=max_errors,
            mean_errors=mean_errors,
            p95_errors=p95_errors,
            witness_count=len(witnesses),
            worst_witnesses=witnesses,
        ),
        rows,
    )


def build_specs() -> list[CaseSpec]:
    return [
        CaseSpec(
            name="quadratic_quotient_representative_invariant",
            kind="good",
            expected=(
                "Linear quotient gluing ignores null representatives and the induced "
                "quadratic energy has zero four-point residual."
            ),
            gluing=linear_quotient_gluing,
            energy=quadratic_energy,
        ),
        CaseSpec(
            name="representative_shift_leak",
            kind="bad",
            expected="Null/gauge representative shifts leak into the gluing output.",
            gluing=representative_shift_leak_gluing,
            energy=quadratic_energy,
        ),
        CaseSpec(
            name="nonlinear_gluing_quotient",
            kind="bad",
            expected="Quotient-only but nonlinear gluing breaks additivity and scalar compatibility.",
            gluing=nonlinear_quotient_gluing,
            energy=quadratic_energy,
        ),
        CaseSpec(
            name="p_norm_nonquadratic_near_miss",
            kind="bad",
            expected=(
                "Representative-invariant linear gluing with a two-homogeneous "
                "non-Hilbert p-norm energy fails four-point cancellation."
            ),
            gluing=p_norm_near_miss_gluing,
            energy=p_norm_two_homogeneous_energy,
        ),
        CaseSpec(
            name="asymmetric_cross_term",
            kind="bad",
            expected="An asymmetric quotient cross-term breaks the gluing/parallelogram law.",
            gluing=asymmetric_cross_term_gluing,
            energy=quadratic_energy,
        ),
    ]


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dimension", type=int, default=4)
    parser.add_argument("--samples", type=int, default=512)
    parser.add_argument("--tolerance", type=float, default=1.0e-10)
    parser.add_argument("--bad-floor", type=float, default=1.0e-3)
    parser.add_argument("--json-output", type=Path, default=DEFAULT_JSON_OUTPUT)
    parser.add_argument("--json", action="store_true", help="Emit JSON to stdout.")
    return parser.parse_args(argv)


def validate_args(args: argparse.Namespace) -> None:
    if args.dimension <= 0:
        raise ValueError("--dimension must be positive")
    if args.samples <= 0:
        raise ValueError("--samples must be positive")
    if args.tolerance <= 0.0:
        raise ValueError("--tolerance must be positive")
    if args.bad_floor <= args.tolerance:
        raise ValueError("--bad-floor must be greater than --tolerance")


def build_summary(args: argparse.Namespace) -> dict[str, object]:
    validate_args(args)
    rng = random.Random(SEED + 101 * args.dimension + args.samples)
    matrix = deterministic_matrix(args.dimension)
    xs = [representative(rng, args.dimension) for _ in range(args.samples)]
    ys = [representative(rng, args.dimension) for _ in range(args.samples)]
    shifts = [null_shift(rng, args.dimension) for _ in range(args.samples)]
    alpha_cycle = [-2.0, -1.3, -0.75, -0.25, 0.5, 1.25, 2.0, 2.75]
    alphas = [alpha_cycle[i % len(alpha_cycle)] for i in range(args.samples)]

    case_metrics: list[CaseMetrics] = []
    all_rows: list[Row] = []
    for spec in build_specs():
        metrics, rows = run_case(
            spec=spec,
            xs=xs,
            ys=ys,
            shifts=shifts,
            alphas=alphas,
            matrix=matrix,
            dimension=args.dimension,
            tolerance=args.tolerance,
            witness_limit=8,
        )
        case_metrics.append(metrics)
        all_rows.extend(rows)

    good = [item for item in case_metrics if item.kind == "good"]
    bad = [item for item in case_metrics if item.kind == "bad"]
    by_name = {item.name: item for item in case_metrics}
    visible_bad = [
        item for item in bad if max(item.max_errors.values(), default=0.0) >= args.bad_floor
    ]
    validation_flags = {
        "promotion_is_false": True,
        "diagnostic_only_is_true": True,
        "has_one_good_case": len(good) == 1,
        "has_four_bad_cases": len(bad) == 4,
        "all_good_cases_pass": all(item.observed_pass for item in good),
        "all_bad_cases_fail": all(not item.observed_pass for item in bad),
        "all_bad_cases_visible": len(visible_bad) == len(bad),
        "representative_shift_leak_detected": "representative_shift"
        in by_name["representative_shift_leak"].failed_checks,
        "nonlinear_gluing_detected": {
            "additivity",
            "scalar_compatibility",
            "four_point_residual",
        }.issubset(set(by_name["nonlinear_gluing_quotient"].failed_checks)),
        "p_norm_near_miss_isolated": (
            by_name["p_norm_nonquadratic_near_miss"].representative_invariant
            and by_name["p_norm_nonquadratic_near_miss"].additive
            and by_name["p_norm_nonquadratic_near_miss"].scalar_compatible
            and by_name["p_norm_nonquadratic_near_miss"].energy_two_homogeneous
            and not by_name["p_norm_nonquadratic_near_miss"].four_point_residual_zero
        ),
        "asymmetric_cross_term_detected": "four_point_residual"
        in by_name["asymmetric_cross_term"].failed_checks,
    }
    ok = all(validation_flags.values())

    good_combined = [
        max(item.max_errors.values(), default=0.0) for item in good
    ]
    bad_combined = [
        max(item.max_errors.values(), default=0.0) for item in bad
    ]
    aggregate = {
        "case_count": len(case_metrics),
        "good_case_count": len(good),
        "bad_case_count": len(bad),
        "sample_count": args.samples,
        "row_count": len(all_rows),
        "observed_pass_count": sum(1 for item in case_metrics if item.observed_pass),
        "observed_fail_count": sum(1 for item in case_metrics if not item.observed_pass),
        "all_expected_outcomes_observed": all(
            item.expected_outcome_observed for item in case_metrics
        ),
        "max_good_combined_error": max(good_combined, default=0.0),
        "min_bad_combined_error": min(bad_combined, default=0.0),
        "max_bad_combined_error": max(bad_combined, default=0.0),
    }

    worst_rows = sorted(all_rows, key=lambda row: row.combined_error, reverse=True)[:32]
    return {
        "control": {
            "O": "Lane 6 owner Zeno; unification quotient/four-point stress diagnostic.",
            "R": "Stress representative invariance and four-point residual cancellation under quotient admissibility near-misses.",
            "C": "scripts/unification_quotient_four_point_stress_harness.py",
            "S": "Pure stdlib finite diagnostic; no theorem, Agda proof, or promotion authority.",
            "L": "finite representatives -> quotient gluing cases -> residual metrics -> fail-closed JSON receipt",
            "P": "Separate one quadratic admissible proxy from four bad quotient/nonquadratic/asymmetric obstructions.",
            "G": "promotion=false and diagnostic_only=true are invariant; ok only means diagnostic separation succeeded.",
            "F": "Does not prove admissible defect quotient, gluing linearity, four-point cancellation, parallelogram, or terminal unification.",
        },
        "ok": ok,
        "promotion": False,
        "diagnostic_only": True,
        "parameters": {
            "dimension": args.dimension,
            "ambient_dimension": 2 * args.dimension,
            "samples": args.samples,
            "tolerance": args.tolerance,
            "bad_floor": args.bad_floor,
            "seed": SEED,
        },
        "good_cases": [asdict(item) for item in good],
        "bad_cases": [asdict(item) for item in bad],
        "aggregate": aggregate,
        "validation_flags": validation_flags,
        "rows": [asdict(row) for row in worst_rows],
    }


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    summary = build_summary(args)
    if args.json_output:
        args.json_output.parent.mkdir(parents=True, exist_ok=True)
        args.json_output.write_text(
            json.dumps(summary, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
    if args.json:
        print(json.dumps(summary, indent=2, sort_keys=True))
    else:
        aggregate = summary["aggregate"]
        print("unification_quotient_four_point_stress_harness")
        print(f"ok={summary['ok']}")
        print(f"promotion={summary['promotion']}")
        print(f"diagnostic_only={summary['diagnostic_only']}")
        print(f"cases={aggregate['case_count']} samples={aggregate['sample_count']}")
        print(f"max_good_combined_error={aggregate['max_good_combined_error']:.6g}")
        print(f"min_bad_combined_error={aggregate['min_bad_combined_error']:.6g}")
    return 0 if summary["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
