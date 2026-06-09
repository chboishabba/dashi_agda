#!/usr/bin/env python3
"""YM Hamiltonian domination spectral-margin budget proxy harness.

This pure-stdlib diagnostic models small finite symmetric matrices for a
Hamiltonian domination budget on a gauge/vacuum quotient sector:

    H >= c_delta * Delta + c_hol * Hol - E

after projection.  It checks deterministic good and bad cases for quotient
stability, holonomy control, kinetic strength, spectral near-zero pollution,
and stability of the E-dominated margin.

The output is a diagnostic receipt only.  It is not a proof of Yang-Mills
Hamiltonian domination, a continuum mass gap, OS transfer, or any Clay claim.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Sequence


Matrix = list[list[float]]

DEFAULT_OUTPUT = Path("outputs/ym_domination_spectral_margin_proxy_harness.json")


@dataclass(frozen=True)
class Parameters:
    dimension: int
    quotient_dimension: int
    c_delta: float
    c_hol: float
    tolerance: float
    jacobi_sweeps: int
    holonomy_gap_floor: float
    h_gap_floor: float
    domination_margin_floor: float
    pollution_floor: float


@dataclass(frozen=True)
class EigenSummary:
    min: float | None
    max: float | None
    first_gap: float | None
    min_positive_gap: float | None
    values: list[float]


@dataclass(frozen=True)
class MarginSummary:
    domination_min_eigenvalue: float | None
    e_budget_norm_bound: float
    e_d_margin_min_eigenvalue: float | None
    h_minus_e_min_eigenvalue: float | None
    h_gap: float | None
    holonomy_min_eigenvalue: float | None
    holonomy_gap: float | None
    delta_gap: float | None
    pollution_distance_to_zero: float | None


@dataclass(frozen=True)
class CaseSummary:
    name: str
    description: str
    expected_pass: bool
    passed_proxy_checks: bool
    dimension: int
    quotient_dimension: int
    max_symmetry_error: float
    projector_idempotence_error: float
    projector_symmetry_error: float
    quotient_commutator_error: dict[str, float]
    eigenvalue_summaries: dict[str, EigenSummary]
    margin_summary: MarginSummary
    checks: dict[str, bool]
    failure_reasons: list[str]


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dimension", type=int, default=6)
    parser.add_argument("--quotient-dimension", type=int, default=4)
    parser.add_argument("--c-delta", type=float, default=0.72)
    parser.add_argument("--c-hol", type=float, default=0.64)
    parser.add_argument("--tolerance", type=float, default=1.0e-9)
    parser.add_argument("--jacobi-sweeps", type=int, default=100)
    parser.add_argument("--holonomy-gap-floor", type=float, default=0.18)
    parser.add_argument("--h-gap-floor", type=float, default=0.30)
    parser.add_argument("--domination-margin-floor", type=float, default=0.08)
    parser.add_argument("--pollution-floor", type=float, default=0.08)
    parser.add_argument("--json-output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--json", action="store_true", help="Emit compact JSON to stdout.")
    return parser.parse_args(argv)


def validate_args(args: argparse.Namespace) -> None:
    if args.dimension < 3:
        raise ValueError("--dimension must be at least 3")
    if not (1 <= args.quotient_dimension < args.dimension):
        raise ValueError("--quotient-dimension must be between 1 and dimension - 1")
    if args.c_delta < 0.0 or args.c_hol < 0.0:
        raise ValueError("--c-delta and --c-hol must be nonnegative")
    if args.tolerance <= 0.0:
        raise ValueError("--tolerance must be positive")
    if args.jacobi_sweeps <= 0:
        raise ValueError("--jacobi-sweeps must be positive")
    if args.holonomy_gap_floor <= 0.0:
        raise ValueError("--holonomy-gap-floor must be positive")
    if args.h_gap_floor <= 0.0:
        raise ValueError("--h-gap-floor must be positive")
    if args.domination_margin_floor <= 0.0:
        raise ValueError("--domination-margin-floor must be positive")
    if args.pollution_floor <= 0.0:
        raise ValueError("--pollution-floor must be positive")


def zero_matrix(rows: int, cols: int) -> Matrix:
    return [[0.0 for _ in range(cols)] for _ in range(rows)]


def diagonal(values: Sequence[float], dimension: int) -> Matrix:
    matrix = zero_matrix(dimension, dimension)
    for index, value in enumerate(values[:dimension]):
        matrix[index][index] = float(value)
    return matrix


def identity(dimension: int) -> Matrix:
    return diagonal([1.0] * dimension, dimension)


def identity_projector(dimension: int, quotient_dimension: int) -> Matrix:
    projector = zero_matrix(dimension, dimension)
    for index in range(quotient_dimension):
        projector[index][index] = 1.0
    return projector


def transpose(matrix: Matrix) -> Matrix:
    if not matrix:
        return []
    return [list(row) for row in zip(*matrix)]


def matmul(left: Matrix, right: Matrix) -> Matrix:
    if not left or not right:
        return []
    right_t = transpose(right)
    return [[sum(a * b for a, b in zip(row, col)) for col in right_t] for row in left]


def add(left: Matrix, right: Matrix) -> Matrix:
    return [
        [a + b for a, b in zip(left_row, right_row)]
        for left_row, right_row in zip(left, right)
    ]


def sub(left: Matrix, right: Matrix) -> Matrix:
    return [
        [a - b for a, b in zip(left_row, right_row)]
        for left_row, right_row in zip(left, right)
    ]


def scale(alpha: float, matrix: Matrix) -> Matrix:
    return [[alpha * value for value in row] for row in matrix]


def max_abs(matrix: Matrix) -> float:
    return max((abs(value) for row in matrix for value in row), default=0.0)


def row_sum_norm_bound(matrix: Matrix) -> float:
    return max((sum(abs(value) for value in row) for row in matrix), default=0.0)


def symmetry_error(matrix: Matrix) -> float:
    return max_abs(sub(matrix, transpose(matrix)))


def commutator_error(matrix: Matrix, projector: Matrix) -> float:
    return max_abs(sub(matmul(matrix, projector), matmul(projector, matrix)))


def quotient_block(matrix: Matrix, quotient_dimension: int) -> Matrix:
    return [row[:quotient_dimension] for row in matrix[:quotient_dimension]]


def jacobi_eigenvalues_symmetric(matrix: Matrix, sweeps: int, tolerance: float) -> list[float]:
    """Return sorted eigenvalues for a small real symmetric matrix."""
    n = len(matrix)
    if n == 0:
        return []
    a = [row[:] for row in matrix]
    for _ in range(sweeps):
        p = 0
        q = 1 if n > 1 else 0
        max_off = 0.0
        for i in range(n):
            for j in range(i + 1, n):
                candidate = abs(a[i][j])
                if candidate > max_off:
                    max_off = candidate
                    p, q = i, j
        if max_off <= tolerance:
            break
        apq = a[p][q]
        if abs(apq) <= tolerance:
            continue

        app = a[p][p]
        aqq = a[q][q]
        tau = (aqq - app) / (2.0 * apq)
        sign = 1.0 if tau >= 0.0 else -1.0
        t = sign / (abs(tau) + math.sqrt(1.0 + tau * tau))
        c = 1.0 / math.sqrt(1.0 + t * t)
        s = t * c

        for k in range(n):
            if k != p and k != q:
                akp = a[k][p]
                akq = a[k][q]
                a[k][p] = c * akp - s * akq
                a[p][k] = a[k][p]
                a[k][q] = s * akp + c * akq
                a[q][k] = a[k][q]

        a[p][p] = c * c * app - 2.0 * s * c * apq + s * s * aqq
        a[q][q] = s * s * app + 2.0 * s * c * apq + c * c * aqq
        a[p][q] = 0.0
        a[q][p] = 0.0

    return sorted(a[i][i] for i in range(n))


def eigen_summary(eigenvalues: Sequence[float], tolerance: float) -> EigenSummary:
    ordered = sorted(eigenvalues)
    if not ordered:
        return EigenSummary(None, None, None, None, [])
    gaps = [ordered[index + 1] - ordered[index] for index in range(len(ordered) - 1)]
    positive_gaps = [gap for gap in gaps if gap > tolerance]
    return EigenSummary(
        min=ordered[0],
        max=ordered[-1],
        first_gap=gaps[0] if gaps else None,
        min_positive_gap=min(positive_gaps) if positive_gaps else None,
        values=[round(value, 12) for value in ordered],
    )


def gap_after_vacuum(eigenvalues: Sequence[float]) -> float | None:
    ordered = sorted(eigenvalues)
    if len(ordered) < 2:
        return None
    return ordered[1] - ordered[0]


def min_abs_eigenvalue(eigenvalues: Sequence[float]) -> float | None:
    if not eigenvalues:
        return None
    return min(abs(value) for value in eigenvalues)


def pad_diagonal(quotient_values: Sequence[float], dimension: int, tail_start: float) -> Matrix:
    values = list(quotient_values)
    while len(values) < dimension:
        values.append(tail_start + 0.27 * (len(values) - len(quotient_values)))
    return diagonal(values, dimension)


def add_symmetric_band(matrix: Matrix, quotient_dimension: int, scale_factor: float) -> Matrix:
    result = [row[:] for row in matrix]
    for i in range(quotient_dimension - 1):
        value = scale_factor * (1.0 + 0.2 * i)
        result[i][i + 1] += value
        result[i + 1][i] += value
    return result


def base_delta(dimension: int, quotient_dimension: int, strength: float) -> Matrix:
    quotient_values = [strength * (0.22 + 0.86 * i) for i in range(quotient_dimension)]
    return pad_diagonal(quotient_values, dimension, tail_start=4.2)


def base_holonomy(dimension: int, quotient_dimension: int, floor: float) -> Matrix:
    quotient_values = [floor + 0.38 * i for i in range(quotient_dimension)]
    return pad_diagonal(quotient_values, dimension, tail_start=3.1)


def base_error(dimension: int, quotient_dimension: int, diagonal_size: float, offdiag_size: float) -> Matrix:
    values = [diagonal_size * (1.0 + 0.1 * i) for i in range(quotient_dimension)]
    error = pad_diagonal(values, dimension, tail_start=0.05)
    for i in range(quotient_dimension - 1):
        error[i][i + 1] = offdiag_size
        error[i + 1][i] = offdiag_size
    return error


def comparison_operator(delta: Matrix, hol: Matrix, error: Matrix, params: Parameters) -> Matrix:
    return sub(add(scale(params.c_delta, delta), scale(params.c_hol, hol)), error)


def stable_hamiltonian(delta: Matrix, hol: Matrix, error: Matrix, params: Parameters, extra: Sequence[float]) -> Matrix:
    h = add(comparison_operator(delta, hol, error, params), diagonal(extra, len(delta)))
    return add_symmetric_band(h, params.quotient_dimension, 0.018)


def case_matrices(name: str, params: Parameters) -> tuple[Matrix, Matrix, Matrix, Matrix]:
    dim = params.dimension
    qdim = params.quotient_dimension

    if name == "dominated_quotient_sector":
        delta = base_delta(dim, qdim, strength=1.0)
        hol = base_holonomy(dim, qdim, floor=0.36)
        error = base_error(dim, qdim, diagonal_size=0.035, offdiag_size=0.006)
        h = stable_hamiltonian(delta, hol, error, params, [0.34, 0.48, 0.63, 0.82, 1.1, 1.25])
        return h, delta, hol, error

    if name == "holonomy_controlled_gap":
        delta = base_delta(dim, qdim, strength=0.72)
        hol = base_holonomy(dim, qdim, floor=0.62)
        error = base_error(dim, qdim, diagonal_size=0.025, offdiag_size=0.004)
        h = stable_hamiltonian(delta, hol, error, params, [0.28, 0.52, 0.76, 0.98, 1.12, 1.3])
        return h, delta, hol, error

    if name == "stable_e_d_margin":
        delta = base_delta(dim, qdim, strength=0.9)
        hol = base_holonomy(dim, qdim, floor=0.42)
        error = base_error(dim, qdim, diagonal_size=0.018, offdiag_size=0.003)
        h = stable_hamiltonian(delta, hol, error, params, [0.22, 0.39, 0.58, 0.78, 1.05, 1.22])
        return h, delta, hol, error

    if name == "weak_kinetic_term":
        delta = base_delta(dim, qdim, strength=0.035)
        hol = base_holonomy(dim, qdim, floor=0.24)
        error = base_error(dim, qdim, diagonal_size=0.03, offdiag_size=0.005)
        h = stable_hamiltonian(delta, hol, error, params, [0.02, 0.025, 0.03, 0.04, 0.6, 0.7])
        return h, delta, hol, error

    if name == "missing_holonomy_control":
        delta = base_delta(dim, qdim, strength=0.88)
        hol = base_holonomy(dim, qdim, floor=1.0e-5)
        error = base_error(dim, qdim, diagonal_size=0.026, offdiag_size=0.004)
        h = stable_hamiltonian(delta, hol, error, params, [0.3, 0.35, 0.48, 0.62, 1.0, 1.1])
        return h, delta, hol, error

    if name == "spectral_pollution_near_zero":
        delta = base_delta(dim, qdim, strength=0.78)
        hol = base_holonomy(dim, qdim, floor=0.31)
        error = base_error(dim, qdim, diagonal_size=0.028, offdiag_size=0.004)
        h = stable_hamiltonian(delta, hol, error, params, [0.26, 0.37, 0.49, 0.65, 1.0, 1.2])
        h[0][0] = 0.012
        h[0][1] = 0.0
        h[1][0] = 0.0
        return h, delta, hol, error

    raise ValueError(f"unknown case: {name}")


def evaluate_case(
    name: str,
    description: str,
    expected_pass: bool,
    params: Parameters,
) -> CaseSummary:
    h, delta, hol, error = case_matrices(name, params)
    projector = identity_projector(params.dimension, params.quotient_dimension)
    qh = quotient_block(h, params.quotient_dimension)
    qd = quotient_block(delta, params.quotient_dimension)
    qhol = quotient_block(hol, params.quotient_dimension)
    qe = quotient_block(error, params.quotient_dimension)
    qcomparison = comparison_operator(qd, qhol, qe, params)
    qdomination = sub(qh, qcomparison)
    qh_minus_e = sub(qh, qe)
    qe_d_margin = sub(add(scale(params.c_delta, qd), scale(params.c_hol, qhol)), scale(row_sum_norm_bound(qe), identity(params.quotient_dimension)))

    eigens = {
        "H_quotient": jacobi_eigenvalues_symmetric(qh, params.jacobi_sweeps, params.tolerance),
        "Delta_quotient": jacobi_eigenvalues_symmetric(qd, params.jacobi_sweeps, params.tolerance),
        "Hol_quotient": jacobi_eigenvalues_symmetric(qhol, params.jacobi_sweeps, params.tolerance),
        "E_quotient": jacobi_eigenvalues_symmetric(qe, params.jacobi_sweeps, params.tolerance),
        "comparison_quotient": jacobi_eigenvalues_symmetric(qcomparison, params.jacobi_sweeps, params.tolerance),
        "domination_residual": jacobi_eigenvalues_symmetric(qdomination, params.jacobi_sweeps, params.tolerance),
        "H_minus_E": jacobi_eigenvalues_symmetric(qh_minus_e, params.jacobi_sweeps, params.tolerance),
        "E_d_margin_proxy": jacobi_eigenvalues_symmetric(qe_d_margin, params.jacobi_sweeps, params.tolerance),
    }
    summaries = {key: eigen_summary(values, params.tolerance) for key, values in eigens.items()}

    h_gap = gap_after_vacuum(eigens["H_quotient"])
    hol_gap = gap_after_vacuum(eigens["Hol_quotient"])
    delta_gap = gap_after_vacuum(eigens["Delta_quotient"])
    pollution_distance = min_abs_eigenvalue(eigens["H_quotient"])
    margin = MarginSummary(
        domination_min_eigenvalue=summaries["domination_residual"].min,
        e_budget_norm_bound=row_sum_norm_bound(qe),
        e_d_margin_min_eigenvalue=summaries["E_d_margin_proxy"].min,
        h_minus_e_min_eigenvalue=summaries["H_minus_E"].min,
        h_gap=h_gap,
        holonomy_min_eigenvalue=summaries["Hol_quotient"].min,
        holonomy_gap=hol_gap,
        delta_gap=delta_gap,
        pollution_distance_to_zero=pollution_distance,
    )

    max_sym = max(symmetry_error(matrix) for matrix in (h, delta, hol, error))
    commutators = {
        "H": commutator_error(h, projector),
        "Delta": commutator_error(delta, projector),
        "Hol": commutator_error(hol, projector),
        "E": commutator_error(error, projector),
    }
    checks = {
        "symmetric_inputs": max_sym <= params.tolerance,
        "projector_valid": max_abs(sub(matmul(projector, projector), projector)) <= params.tolerance
        and symmetry_error(projector) <= params.tolerance,
        "quotient_stable": max(commutators.values()) <= params.tolerance,
        "domination_margin_positive": (margin.domination_min_eigenvalue or -math.inf)
        >= params.domination_margin_floor,
        "holonomy_controlled_gap": (margin.holonomy_min_eigenvalue or -math.inf)
        >= params.holonomy_gap_floor,
        "kinetic_gap_present": (margin.delta_gap or -math.inf) >= params.h_gap_floor,
        "h_gap_present": (margin.h_gap or -math.inf) >= params.h_gap_floor,
        "stable_e_d_margin": (margin.e_d_margin_min_eigenvalue or -math.inf) > 0.0,
        "no_near_zero_pollution": (margin.pollution_distance_to_zero or 0.0) >= params.pollution_floor,
    }
    passed = all(checks.values())
    failures = [key for key, value in checks.items() if not value]

    return CaseSummary(
        name=name,
        description=description,
        expected_pass=expected_pass,
        passed_proxy_checks=passed,
        dimension=params.dimension,
        quotient_dimension=params.quotient_dimension,
        max_symmetry_error=max_sym,
        projector_idempotence_error=max_abs(sub(matmul(projector, projector), projector)),
        projector_symmetry_error=symmetry_error(projector),
        quotient_commutator_error=commutators,
        eigenvalue_summaries=summaries,
        margin_summary=margin,
        checks=checks,
        failure_reasons=failures,
    )


def aggregate_metrics(good_cases: Sequence[CaseSummary], bad_cases: Sequence[CaseSummary]) -> dict[str, Any]:
    all_cases = list(good_cases) + list(bad_cases)
    margins = [
        case.margin_summary.domination_min_eigenvalue
        for case in all_cases
        if case.margin_summary.domination_min_eigenvalue is not None
    ]
    h_gaps = [case.margin_summary.h_gap for case in all_cases if case.margin_summary.h_gap is not None]
    hol_gaps = [
        case.margin_summary.holonomy_gap
        for case in all_cases
        if case.margin_summary.holonomy_gap is not None
    ]
    return {
        "case_count": len(all_cases),
        "good_case_count": len(good_cases),
        "bad_case_count": len(bad_cases),
        "good_cases_passed": sum(1 for case in good_cases if case.passed_proxy_checks),
        "bad_cases_failed": sum(1 for case in bad_cases if not case.passed_proxy_checks),
        "min_domination_margin": min(margins) if margins else None,
        "max_domination_margin": max(margins) if margins else None,
        "min_h_gap": min(h_gaps) if h_gaps else None,
        "min_holonomy_gap": min(hol_gaps) if hol_gaps else None,
        "classification_accuracy": sum(
            1 for case in all_cases if case.passed_proxy_checks == case.expected_pass
        )
        / float(len(all_cases)),
    }


def build_report(params: Parameters) -> dict[str, Any]:
    good_specs = (
        ("dominated_quotient_sector", "H dominates c_delta*Delta + c_hol*Hol - E on the quotient sector."),
        ("holonomy_controlled_gap", "Holonomy floor supplies an explicit quotient gap budget."),
        ("stable_e_d_margin", "Small E leaves a positive Delta/Hol margin after row-sum budget subtraction."),
    )
    bad_specs = (
        ("weak_kinetic_term", "Kinetic Delta gap is too weak to support the spectral-margin gate."),
        ("missing_holonomy_control", "Holonomy control is nearly absent in the vacuum-adjacent sector."),
        ("spectral_pollution_near_zero", "A near-zero H eigenvalue pollutes the quotient spectrum."),
    )
    good_cases = [evaluate_case(name, desc, True, params) for name, desc in good_specs]
    bad_cases = [evaluate_case(name, desc, False, params) for name, desc in bad_specs]
    metrics = aggregate_metrics(good_cases, bad_cases)
    validation_flags = {
        "all_good_cases_pass": all(case.passed_proxy_checks for case in good_cases),
        "all_bad_cases_fail": all(not case.passed_proxy_checks for case in bad_cases),
        "classification_matches_expectation": metrics["classification_accuracy"] == 1.0,
        "stdlib_only": True,
        "deterministic": True,
        "diagnostic_only": True,
        "promotion_blocked": True,
    }
    ok = all(validation_flags.values())
    return {
        "ok": ok,
        "promotion": False,
        "diagnostic_only": True,
        "parameters": asdict(params),
        "good_cases": [asdict(case) for case in good_cases],
        "bad_cases": [asdict(case) for case in bad_cases],
        "aggregate_metrics": metrics,
        "validation_flags": validation_flags,
    }


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    validate_args(args)
    params = Parameters(
        dimension=args.dimension,
        quotient_dimension=args.quotient_dimension,
        c_delta=args.c_delta,
        c_hol=args.c_hol,
        tolerance=args.tolerance,
        jacobi_sweeps=args.jacobi_sweeps,
        holonomy_gap_floor=args.holonomy_gap_floor,
        h_gap_floor=args.h_gap_floor,
        domination_margin_floor=args.domination_margin_floor,
        pollution_floor=args.pollution_floor,
    )
    report = build_report(params)
    args.json_output.parent.mkdir(parents=True, exist_ok=True)
    args.json_output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    if args.json:
        print(json.dumps(report, sort_keys=True))
    else:
        print(
            "YM domination spectral-margin proxy: "
            f"ok={report['ok']} output={args.json_output}"
        )
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
