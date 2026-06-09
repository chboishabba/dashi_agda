#!/usr/bin/env python3
"""Finite proxy harness for unification gluing quotient admissibility.

This diagnostic models an ambient finite-dimensional representative space
R^(q+n) with quotient coordinates in the first q entries and null/gauge
coordinates in the last n entries.  A quotient-admissible gluing proxy should:

  * be invariant under changes of null representative;
  * be additive on quotient classes;
  * be compatible with scalar multiplication;
  * induce a quadratic four-point/parallelogram residual that cancels.

The harness emits deterministic good and bad examples.  It is diagnostic only:
it proves no quotient theorem and always reports promotion=false.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Callable, Sequence


Vector = list[float]
Matrix = list[list[float]]
Operator = Callable[[Vector, int, Matrix], Vector]
Energy = Callable[[Vector, int, Matrix, Operator], float]

DEFAULT_JSON_OUTPUT = Path(
    "outputs/unification_gluing_quotient_admissibility_proxy_harness.json"
)


def add(x: Sequence[float], y: Sequence[float]) -> Vector:
    return [a + b for a, b in zip(x, y)]


def sub(x: Sequence[float], y: Sequence[float]) -> Vector:
    return [a - b for a, b in zip(x, y)]


def scale(alpha: float, x: Sequence[float]) -> Vector:
    return [alpha * value for value in x]


def dot(x: Sequence[float], y: Sequence[float]) -> float:
    return sum(a * b for a, b in zip(x, y))


def mat_vec(matrix: Matrix, vector: Sequence[float]) -> Vector:
    return [dot(row, vector) for row in matrix]


def norm2(x: Sequence[float]) -> float:
    return math.sqrt(dot(x, x))


def norm2_sq(x: Sequence[float]) -> float:
    return dot(x, x)


def l1_sq(x: Sequence[float]) -> float:
    return sum(abs(value) for value in x) ** 2


def quotient(x: Sequence[float], quotient_dim: int) -> Vector:
    return list(x[:quotient_dim])


def null_part(x: Sequence[float], quotient_dim: int) -> Vector:
    return list(x[quotient_dim:])


def deterministic_matrix(quotient_dim: int, output_dim: int) -> Matrix:
    """Stable full-rank-looking rectangular matrix with mixed couplings."""
    matrix: Matrix = []
    for i in range(output_dim):
        row: Vector = []
        for j in range(quotient_dim):
            diagonal = 1.0 if i == j else 0.0
            skew = 0.07 * (i - j)
            low_rank = 0.025 * (i + 1) * (j + 2)
            alternating = 0.013 * ((-1.0) ** (i + j)) * (i + j + 1)
            row.append(diagonal + skew + low_rank + alternating)
        matrix.append(row)
    return matrix


def deterministic_representatives(
    ambient_dim: int, quotient_dim: int, radius: int
) -> list[Vector]:
    values = list(range(-radius, radius + 1))
    reps: list[Vector] = []
    for index in range(max(64, ambient_dim * 24)):
        row: Vector = []
        for coord in range(ambient_dim):
            raw = values[(index * (coord + 2) + coord * coord + 3) % len(values)]
            row.append(raw / max(1.0, float(radius)))
        if any(abs(value) > 0.0 for value in quotient(row, quotient_dim)):
            reps.append(row)
    return reps


def deterministic_null_shifts(
    ambient_dim: int, quotient_dim: int, radius: int
) -> list[Vector]:
    null_dim = ambient_dim - quotient_dim
    shifts: list[Vector] = []
    for index in range(max(16, null_dim * 12)):
        head = [0.0] * quotient_dim
        tail: Vector = []
        for coord in range(null_dim):
            raw = ((index + 1) * (coord + 3) + coord) % (2 * radius + 1) - radius
            tail.append(raw / max(1.0, float(radius)))
        if any(abs(value) > 0.0 for value in tail):
            shifts.append(head + tail)
    return shifts


def linear_quotient_operator(x: Vector, quotient_dim: int, matrix: Matrix) -> Vector:
    return mat_vec(matrix, quotient(x, quotient_dim))


def representative_leak_operator(x: Vector, quotient_dim: int, matrix: Matrix) -> Vector:
    out = linear_quotient_operator(x, quotient_dim, matrix)
    null = null_part(x, quotient_dim)
    if out and null:
        out[0] += 0.31 * sum((i + 1) * value for i, value in enumerate(null))
    if len(out) > 1 and null:
        out[1] -= 0.17 * sum(value * value for value in null)
    return out


def nonlinear_operator(x: Vector, quotient_dim: int, matrix: Matrix) -> Vector:
    q = quotient(x, quotient_dim)
    out = linear_quotient_operator(x, quotient_dim, matrix)
    if out:
        out[0] += 0.19 * q[0] * q[-1]
    if len(out) > 1:
        out[1] += 0.11 * q[0] * q[0]
    if len(out) > 2:
        out[2] -= 0.07 * sum(value * value for value in q)
    return out


def norm_like_operator(x: Vector, quotient_dim: int, matrix: Matrix) -> Vector:
    # The map itself is quotient-linear; the induced "energy" below is not
    # Hilbert/quadratic, giving the intended two-homogeneous near miss.
    return linear_quotient_operator(x, quotient_dim, matrix)


def quadratic_energy(
    x: Vector, quotient_dim: int, matrix: Matrix, operator: Operator
) -> float:
    return norm2_sq(operator(x, quotient_dim, matrix))


def l1_norm_like_energy(
    x: Vector, quotient_dim: int, matrix: Matrix, operator: Operator
) -> float:
    return l1_sq(operator(x, quotient_dim, matrix))


@dataclass(frozen=True)
class CaseSpec:
    name: str
    kind: str
    expected: str
    operator: Operator
    energy: Energy


@dataclass(frozen=True)
class CaseMetrics:
    name: str
    kind: str
    expected: str
    observed_pass: bool
    expected_outcome_observed: bool
    representative_invariance: bool
    additivity: bool
    scalar_compatibility: bool
    two_homogeneity_energy: bool
    four_point_residual_cancellation: bool
    failed_checks: list[str]
    max_errors: dict[str, float]
    mean_errors: dict[str, float]
    witness_count: int
    worst_witnesses: list[dict[str, object]]


def four_point_residual(
    energy: Energy,
    operator: Operator,
    x: Vector,
    y: Vector,
    quotient_dim: int,
    matrix: Matrix,
) -> float:
    return (
        energy(add(x, y), quotient_dim, matrix, operator)
        + energy(sub(x, y), quotient_dim, matrix, operator)
        - 2.0 * energy(x, quotient_dim, matrix, operator)
        - 2.0 * energy(y, quotient_dim, matrix, operator)
    )


def energy_homogeneity_error(
    energy: Energy,
    operator: Operator,
    alpha: float,
    x: Vector,
    quotient_dim: int,
    matrix: Matrix,
) -> float:
    lhs = energy(scale(alpha, x), quotient_dim, matrix, operator)
    rhs = alpha * alpha * energy(x, quotient_dim, matrix, operator)
    return abs(lhs - rhs)


def append_witness(
    witnesses: list[dict[str, object]],
    candidate: dict[str, object],
    limit: int,
) -> None:
    witnesses.append(candidate)
    witnesses.sort(key=lambda item: float(item["combined_error"]), reverse=True)
    del witnesses[limit:]


def run_case(
    spec: CaseSpec,
    representatives: Sequence[Vector],
    null_shifts: Sequence[Vector],
    scalars: Sequence[float],
    matrix: Matrix,
    quotient_dim: int,
    tolerance: float,
    witness_limit: int,
) -> CaseMetrics:
    rep_errors: list[float] = []
    add_errors: list[float] = []
    scalar_errors: list[float] = []
    homogeneity_errors: list[float] = []
    four_point_errors: list[float] = []
    witnesses: list[dict[str, object]] = []

    for index, x in enumerate(representatives):
        y = representatives[(3 * index + 5) % len(representatives)]
        shift = null_shifts[index % len(null_shifts)]
        alpha = scalars[index % len(scalars)]

        gx = spec.operator(x, quotient_dim, matrix)
        gy = spec.operator(y, quotient_dim, matrix)
        rep_error = norm2(sub(spec.operator(add(x, shift), quotient_dim, matrix), gx))
        add_error = norm2(
            sub(spec.operator(add(x, y), quotient_dim, matrix), add(gx, gy))
        )
        scalar_error = norm2(
            sub(spec.operator(scale(alpha, x), quotient_dim, matrix), scale(alpha, gx))
        )
        homogeneity_error = energy_homogeneity_error(
            spec.energy, spec.operator, alpha, x, quotient_dim, matrix
        )
        fp_error = abs(
            four_point_residual(spec.energy, spec.operator, x, y, quotient_dim, matrix)
        )

        rep_errors.append(rep_error)
        add_errors.append(add_error)
        scalar_errors.append(scalar_error)
        homogeneity_errors.append(homogeneity_error)
        four_point_errors.append(fp_error)

        combined = max(
            rep_error, add_error, scalar_error, homogeneity_error, fp_error
        )
        if combined > tolerance or len(witnesses) < witness_limit:
            append_witness(
                witnesses,
                {
                    "sample": index,
                    "alpha": alpha,
                    "quotient_x": quotient(x, quotient_dim),
                    "quotient_y": quotient(y, quotient_dim),
                    "null_shift": null_part(shift, quotient_dim),
                    "representative_error": rep_error,
                    "additivity_error": add_error,
                    "scalar_error": scalar_error,
                    "two_homogeneity_energy_error": homogeneity_error,
                    "four_point_residual_error": fp_error,
                    "combined_error": combined,
                },
                witness_limit,
            )

    max_errors = {
        "representative_invariance": max(rep_errors, default=0.0),
        "additivity": max(add_errors, default=0.0),
        "scalar_compatibility": max(scalar_errors, default=0.0),
        "two_homogeneity_energy": max(homogeneity_errors, default=0.0),
        "four_point_residual_cancellation": max(four_point_errors, default=0.0),
    }
    mean_errors = {
        "representative_invariance": sum(rep_errors) / len(rep_errors),
        "additivity": sum(add_errors) / len(add_errors),
        "scalar_compatibility": sum(scalar_errors) / len(scalar_errors),
        "two_homogeneity_energy": sum(homogeneity_errors) / len(homogeneity_errors),
        "four_point_residual_cancellation": sum(four_point_errors)
        / len(four_point_errors),
    }
    checks = {
        name: value <= tolerance for name, value in max_errors.items()
    }
    failed = [name for name, passed in checks.items() if not passed]
    observed_pass = all(checks.values())
    expected_outcome_observed = (
        observed_pass if spec.kind == "good" else not observed_pass
    )

    return CaseMetrics(
        name=spec.name,
        kind=spec.kind,
        expected=spec.expected,
        observed_pass=observed_pass,
        expected_outcome_observed=expected_outcome_observed,
        representative_invariance=checks["representative_invariance"],
        additivity=checks["additivity"],
        scalar_compatibility=checks["scalar_compatibility"],
        two_homogeneity_energy=checks["two_homogeneity_energy"],
        four_point_residual_cancellation=checks["four_point_residual_cancellation"],
        failed_checks=failed,
        max_errors=max_errors,
        mean_errors=mean_errors,
        witness_count=len(witnesses),
        worst_witnesses=witnesses,
    )


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--ambient-dim", type=int, default=7)
    parser.add_argument("--quotient-dim", type=int, default=4)
    parser.add_argument("--output-dim", type=int, default=4)
    parser.add_argument("--radius", type=int, default=3)
    parser.add_argument("--tolerance", type=float, default=1.0e-10)
    parser.add_argument("--counterexample-min-error", type=float, default=1.0e-3)
    parser.add_argument("--witness-limit", type=int, default=6)
    parser.add_argument("--json-output", type=Path, default=None)
    parser.add_argument("--json", action="store_true", help="Emit JSON to stdout.")
    return parser.parse_args(argv)


def validate_args(args: argparse.Namespace) -> None:
    if args.ambient_dim <= 1:
        raise ValueError("--ambient-dim must be greater than 1")
    if args.quotient_dim <= 0:
        raise ValueError("--quotient-dim must be positive")
    if args.quotient_dim >= args.ambient_dim:
        raise ValueError("--quotient-dim must be smaller than --ambient-dim")
    if args.output_dim <= 0:
        raise ValueError("--output-dim must be positive")
    if args.radius <= 0:
        raise ValueError("--radius must be positive")
    if args.tolerance <= 0.0:
        raise ValueError("--tolerance must be positive")
    if args.counterexample_min_error <= args.tolerance:
        raise ValueError("--counterexample-min-error must exceed --tolerance")
    if args.witness_limit <= 0:
        raise ValueError("--witness-limit must be positive")


def build_summary(args: argparse.Namespace) -> dict[str, object]:
    validate_args(args)
    matrix = deterministic_matrix(args.quotient_dim, args.output_dim)
    representatives = deterministic_representatives(
        args.ambient_dim, args.quotient_dim, args.radius
    )
    null_shifts = deterministic_null_shifts(
        args.ambient_dim, args.quotient_dim, args.radius
    )
    scalars = [-2.0, -1.25, -0.5, 0.0, 0.5, 1.5, 2.25]

    specs = [
        CaseSpec(
            name="linear_quotient_gluing",
            kind="good",
            expected=(
                "Representative-invariant linear quotient operator with quadratic "
                "four-point residual cancellation."
            ),
            operator=linear_quotient_operator,
            energy=quadratic_energy,
        ),
        CaseSpec(
            name="representative_dependent_leak",
            kind="bad",
            expected="Fails because null representatives leak into gluing output.",
            operator=representative_leak_operator,
            energy=quadratic_energy,
        ),
        CaseSpec(
            name="nonlinear_quotient_gluing",
            kind="bad",
            expected="Fails additivity, scalar compatibility, and four-point cancellation.",
            operator=nonlinear_operator,
            energy=quadratic_energy,
        ),
        CaseSpec(
            name="two_homogeneous_norm_like_near_miss",
            kind="bad",
            expected=(
                "Passes quotient-linearity and two-homogeneity but fails the "
                "parallelogram/four-point law."
            ),
            operator=norm_like_operator,
            energy=l1_norm_like_energy,
        ),
    ]
    metrics = [
        run_case(
            spec=spec,
            representatives=representatives,
            null_shifts=null_shifts,
            scalars=scalars,
            matrix=matrix,
            quotient_dim=args.quotient_dim,
            tolerance=args.tolerance,
            witness_limit=args.witness_limit,
        )
        for spec in specs
    ]

    good_cases = [asdict(item) for item in metrics if item.kind == "good"]
    bad_cases = [asdict(item) for item in metrics if item.kind == "bad"]
    by_name = {item.name: item for item in metrics}
    visible_bad = [
        item
        for item in metrics
        if item.kind == "bad"
        and max(item.max_errors.values()) > args.counterexample_min_error
    ]
    validation_flags = {
        "promotion_is_false": True,
        "diagnostic_only_is_true": True,
        "has_one_good_case": len(good_cases) == 1,
        "has_three_bad_cases": len(bad_cases) == 3,
        "all_good_cases_pass": all(item.observed_pass for item in metrics if item.kind == "good"),
        "all_bad_cases_fail": all(not item.observed_pass for item in metrics if item.kind == "bad"),
        "all_bad_cases_visible": len(visible_bad) == 3,
        "representative_leak_detected": "representative_invariance"
        in by_name["representative_dependent_leak"].failed_checks,
        "nonlinear_gluing_detected": {
            "additivity",
            "scalar_compatibility",
            "four_point_residual_cancellation",
        }.issubset(set(by_name["nonlinear_quotient_gluing"].failed_checks)),
        "two_homogeneous_near_miss_is_isolated": (
            by_name["two_homogeneous_norm_like_near_miss"].representative_invariance
            and by_name["two_homogeneous_norm_like_near_miss"].additivity
            and by_name["two_homogeneous_norm_like_near_miss"].scalar_compatibility
            and by_name["two_homogeneous_norm_like_near_miss"].two_homogeneity_energy
            and not by_name[
                "two_homogeneous_norm_like_near_miss"
            ].four_point_residual_cancellation
        ),
    }
    ok = all(validation_flags.values())

    aggregate = {
        "case_count": len(metrics),
        "good_case_count": len(good_cases),
        "bad_case_count": len(bad_cases),
        "observed_pass_count": sum(1 for item in metrics if item.observed_pass),
        "observed_fail_count": sum(1 for item in metrics if not item.observed_pass),
        "max_good_combined_error": max(
            max(item.max_errors.values()) for item in metrics if item.kind == "good"
        ),
        "min_bad_combined_error": min(
            max(item.max_errors.values()) for item in metrics if item.kind == "bad"
        ),
        "all_expected_outcomes_observed": all(
            item.expected_outcome_observed for item in metrics
        ),
    }

    return {
        "control": {
            "O": "Worker Lane 6 Dewey unification gluing quotient admissibility proxy harness.",
            "R": "Finite quotient representatives must support representative-invariant linear gluing and quadratic four-point residual cancellation.",
            "C": "scripts/unification_gluing_quotient_admissibility_proxy_harness.py",
            "S": "Pure stdlib deterministic finite-dimensional diagnostic; no Agda, docs, manifest, or persistent outputs are required.",
            "L": "construct quotient examples -> run good linear case -> run three obstruction cases -> aggregate fail-closed validation flags",
            "P": "Use explicit finite matrices, representative shifts, and scalar tests to separate admissible and inadmissible quotient proxies.",
            "G": "promotion=false and diagnostic_only=true always; this cannot certify the true unification quotient.",
            "F": "Does not construct the real defect quotient or prove admissibility beyond these finite proxy examples.",
        },
        "ok": ok,
        "promotion": False,
        "diagnostic_only": True,
        "parameters": {
            "ambient_dim": args.ambient_dim,
            "quotient_dim": args.quotient_dim,
            "null_dim": args.ambient_dim - args.quotient_dim,
            "output_dim": args.output_dim,
            "radius": args.radius,
            "representative_count": len(representatives),
            "null_shift_count": len(null_shifts),
            "tolerance": args.tolerance,
            "counterexample_min_error": args.counterexample_min_error,
        },
        "validation_flags": validation_flags,
        "aggregate": aggregate,
        "good_cases": good_cases,
        "bad_cases": bad_cases,
    }


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    summary = build_summary(args)
    if args.json_output is not None:
        args.json_output.parent.mkdir(parents=True, exist_ok=True)
        args.json_output.write_text(
            json.dumps(summary, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
    if args.json:
        print(json.dumps(summary, indent=2, sort_keys=True))
    else:
        print("unification gluing quotient admissibility proxy harness")
        print(f"ok={str(summary['ok']).lower()}")
        print("promotion=false")
        print("diagnostic_only=true")
        aggregate = summary["aggregate"]
        print(f"good_cases={aggregate['good_case_count']}")
        print(f"bad_cases={aggregate['bad_case_count']}")
        print(f"max_good_combined_error={aggregate['max_good_combined_error']:.6g}")
        print(f"min_bad_combined_error={aggregate['min_bad_combined_error']:.6g}")
    return 0 if summary["ok"] and not summary["promotion"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
