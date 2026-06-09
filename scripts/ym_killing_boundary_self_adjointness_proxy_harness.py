#!/usr/bin/env python3
"""YM Killing-boundary self-adjointness sensitivity proxy harness.

This deterministic pure-stdlib diagnostic models the finite gate behind the
Killing/full-degree Bruhat-Tits boundary convention:

    symmetric finite form + orthogonal gauge quotient projection
    + no quotient/null leakage + positive quotient spectral margin
    -> finite self-adjointness/domain-stability proxy.

It compares boundary profiles that should pass the proxy checks against
profiles that fail by asymmetry, quotient leakage, non-orthogonal projection,
or spectral-margin collapse.  The receipt is diagnostic only and always keeps
``promotion=false``; it does not prove Yang-Mills Hamiltonian domination,
reflection positivity, OS/Wightman reconstruction, continuum transfer, or any
Clay claim.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Sequence


Matrix = list[list[float]]

DEFAULT_OUTPUT = Path("outputs/ym_killing_boundary_self_adjointness_proxy_harness.json")
TOLERANCE = 1.0e-9
JACOBI_SWEEPS = 96


@dataclass(frozen=True)
class Parameters:
    dimension: int
    quotient_dimension: int
    sweeps: int
    tolerance: float
    spectral_margin_floor: float
    leakage_floor: float


@dataclass(frozen=True)
class BoundaryRow:
    regime: str
    kind: str
    index: int
    expected_pass: bool
    passed_proxy_checks: bool
    projector_idempotence_defect: float
    projector_symmetry_defect: float
    full_symmetry_defect: float
    quotient_symmetry_defect: float
    gauge_null_leakage: float
    quotient_commutator_defect: float
    quotient_eigenvalues: list[float]
    spectral_margin: float
    spectral_diameter: float
    checks: dict[str, bool]
    failure_reasons: list[str]


@dataclass(frozen=True)
class RegimeSummary:
    name: str
    kind: str
    expected_pass: bool
    row_count: int
    rows_passing: int
    rows_failing: int
    max_projector_symmetry_defect: float
    max_full_symmetry_defect: float
    max_gauge_null_leakage: float
    min_spectral_margin: float
    classification_matches_expectation: bool


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dimension", type=int, default=6)
    parser.add_argument("--quotient-dimension", type=int, default=4)
    parser.add_argument("--sweeps", type=int, default=8)
    parser.add_argument("--json-output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--json", action="store_true", help="Emit compact JSON to stdout.")
    return parser.parse_args(argv)


def validate_args(args: argparse.Namespace) -> None:
    if args.dimension < 3:
        raise ValueError("--dimension must be at least 3")
    if not (1 <= args.quotient_dimension < args.dimension):
        raise ValueError("--quotient-dimension must be between 1 and dimension - 1")
    if args.sweeps < 3:
        raise ValueError("--sweeps must be at least 3")


def zero_matrix(rows: int, cols: int) -> Matrix:
    return [[0.0 for _ in range(cols)] for _ in range(rows)]


def identity_projector(dimension: int, quotient_dimension: int) -> Matrix:
    projector = zero_matrix(dimension, dimension)
    for index in range(quotient_dimension):
        projector[index][index] = 1.0
    return projector


def skew_projector(dimension: int, quotient_dimension: int, strength: float) -> Matrix:
    projector = identity_projector(dimension, quotient_dimension)
    outside = quotient_dimension
    projector[0][outside] = strength
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


def sub(left: Matrix, right: Matrix) -> Matrix:
    return [
        [a - b for a, b in zip(left_row, right_row)]
        for left_row, right_row in zip(left, right)
    ]


def max_abs(matrix: Matrix) -> float:
    return max((abs(value) for row in matrix for value in row), default=0.0)


def symmetry_defect(matrix: Matrix) -> float:
    return max_abs(sub(matrix, transpose(matrix)))


def commutator_defect(matrix: Matrix, projector: Matrix) -> float:
    return max_abs(sub(matmul(matrix, projector), matmul(projector, matrix)))


def quotient_block(matrix: Matrix, quotient_dimension: int) -> Matrix:
    return [row[:quotient_dimension] for row in matrix[:quotient_dimension]]


def gauge_null_leakage(matrix: Matrix, quotient_dimension: int) -> float:
    dimension = len(matrix)
    if quotient_dimension >= dimension:
        return 0.0
    leakage = 0.0
    for i in range(quotient_dimension):
        for j in range(quotient_dimension, dimension):
            leakage = max(leakage, abs(matrix[i][j]), abs(matrix[j][i]))
    return leakage


def sorted_eigen_metrics(eigenvalues: Sequence[float]) -> tuple[float, float]:
    if not eigenvalues:
        return 0.0, 0.0
    ordered = sorted(eigenvalues)
    return ordered[0], ordered[-1] - ordered[0]


def jacobi_eigenvalues_symmetric(matrix: Matrix, sweeps: int, tolerance: float) -> list[float]:
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
        if max_off <= tolerance or n == 1:
            break

        app = a[p][p]
        aqq = a[q][q]
        apq = a[p][q]
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


def killing_full_degree_matrix(
    dimension: int,
    quotient_dimension: int,
    index: int,
    sweeps: int,
    quotient_floor: float,
    null_floor: float,
    offdiag_scale: float,
) -> Matrix:
    matrix = zero_matrix(dimension, dimension)
    phase = index / float(max(1, sweeps - 1))
    for i in range(dimension):
        for j in range(i, dimension):
            same_quotient = i < quotient_dimension and j < quotient_dimension
            same_null = i >= quotient_dimension and j >= quotient_dimension
            if same_quotient:
                if i == j:
                    value = quotient_floor + 0.31 * i + 0.025 * phase
                else:
                    value = offdiag_scale * (1.0 + i + j) / float(dimension)
            elif same_null:
                if i == j:
                    value = null_floor + 0.19 * (i - quotient_dimension) + 0.015 * phase
                else:
                    value = 0.04 * offdiag_scale
            else:
                value = 0.0
            matrix[i][j] = value
            matrix[j][i] = value
    return matrix


def summarize_row(
    *,
    regime: str,
    kind: str,
    index: int,
    expected_pass: bool,
    matrix: Matrix,
    projector: Matrix,
    params: Parameters,
) -> BoundaryRow:
    p2_defect = max_abs(sub(matmul(projector, projector), projector))
    p_sym_defect = symmetry_defect(projector)
    h_sym_defect = symmetry_defect(matrix)
    comm_defect = commutator_defect(matrix, projector)
    leakage = gauge_null_leakage(matrix, params.quotient_dimension)
    compressed = matmul(matmul(projector, matrix), projector)
    q_matrix = quotient_block(compressed, params.quotient_dimension)
    q_sym_defect = symmetry_defect(q_matrix)

    eigenvalues = (
        jacobi_eigenvalues_symmetric(q_matrix, JACOBI_SWEEPS, params.tolerance)
        if q_sym_defect <= params.tolerance
        else []
    )
    spectral_margin, spectral_diameter = sorted_eigen_metrics(eigenvalues)

    checks = {
        "projector_idempotent": p2_defect <= params.tolerance,
        "projector_orthogonal": p_sym_defect <= params.tolerance,
        "finite_form_symmetric": h_sym_defect <= params.tolerance,
        "quotient_domain_stable": comm_defect <= params.tolerance,
        "quotient_block_symmetric": q_sym_defect <= params.tolerance,
        "gauge_null_leakage_absent": leakage <= params.leakage_floor,
        "quotient_spectrum_real": len(eigenvalues) == params.quotient_dimension
        and all(math.isfinite(value) for value in eigenvalues),
        "spectral_margin_positive": spectral_margin >= params.spectral_margin_floor,
    }
    passed = all(checks.values())
    return BoundaryRow(
        regime=regime,
        kind=kind,
        index=index,
        expected_pass=expected_pass,
        passed_proxy_checks=passed,
        projector_idempotence_defect=p2_defect,
        projector_symmetry_defect=p_sym_defect,
        full_symmetry_defect=h_sym_defect,
        quotient_symmetry_defect=q_sym_defect,
        gauge_null_leakage=leakage,
        quotient_commutator_defect=comm_defect,
        quotient_eigenvalues=eigenvalues,
        spectral_margin=spectral_margin,
        spectral_diameter=spectral_diameter,
        checks=checks,
        failure_reasons=[name for name, ok in checks.items() if not ok],
    )


def build_rows(params: Parameters) -> list[BoundaryRow]:
    rows: list[BoundaryRow] = []
    good_projector = identity_projector(params.dimension, params.quotient_dimension)

    for index in range(params.sweeps):
        rows.append(
            summarize_row(
                regime="killing_full_degree_boundary",
                kind="good",
                index=index,
                expected_pass=True,
                matrix=killing_full_degree_matrix(
                    params.dimension,
                    params.quotient_dimension,
                    index,
                    params.sweeps,
                    quotient_floor=1.25,
                    null_floor=2.65,
                    offdiag_scale=0.075,
                ),
                projector=good_projector,
                params=params,
            )
        )
        rows.append(
            summarize_row(
                regime="killing_holonomy_buffered_boundary",
                kind="good",
                index=index,
                expected_pass=True,
                matrix=killing_full_degree_matrix(
                    params.dimension,
                    params.quotient_dimension,
                    index,
                    params.sweeps,
                    quotient_floor=0.96,
                    null_floor=2.20,
                    offdiag_scale=0.055,
                ),
                projector=good_projector,
                params=params,
            )
        )

        asymmetric = killing_full_degree_matrix(
            params.dimension,
            params.quotient_dimension,
            index,
            params.sweeps,
            quotient_floor=1.15,
            null_floor=2.35,
            offdiag_scale=0.060,
        )
        if params.quotient_dimension >= 2:
            asymmetric[0][1] += 0.14 + 0.01 * index
        else:
            asymmetric[0][params.quotient_dimension] += 0.14 + 0.01 * index
        rows.append(
            summarize_row(
                regime="asymmetric_boundary_form",
                kind="bad",
                index=index,
                expected_pass=False,
                matrix=asymmetric,
                projector=good_projector,
                params=params,
            )
        )

        leaking = killing_full_degree_matrix(
            params.dimension,
            params.quotient_dimension,
            index,
            params.sweeps,
            quotient_floor=1.05,
            null_floor=2.15,
            offdiag_scale=0.050,
        )
        null_index = params.quotient_dimension
        for q_index in range(params.quotient_dimension):
            value = 0.055 + 0.006 * index + 0.004 * q_index
            leaking[q_index][null_index] = value
            leaking[null_index][q_index] = value
        rows.append(
            summarize_row(
                regime="gauge_null_leaking_boundary",
                kind="bad",
                index=index,
                expected_pass=False,
                matrix=leaking,
                projector=good_projector,
                params=params,
            )
        )

        collapsed = killing_full_degree_matrix(
            params.dimension,
            params.quotient_dimension,
            index,
            params.sweeps,
            quotient_floor=0.020 + 0.006 * index / float(params.sweeps),
            null_floor=2.00,
            offdiag_scale=0.002,
        )
        rows.append(
            summarize_row(
                regime="induced_ball_spectral_collapse_boundary",
                kind="bad",
                index=index,
                expected_pass=False,
                matrix=collapsed,
                projector=good_projector,
                params=params,
            )
        )

        rows.append(
            summarize_row(
                regime="nonorthogonal_gauge_projection_boundary",
                kind="bad",
                index=index,
                expected_pass=False,
                matrix=killing_full_degree_matrix(
                    params.dimension,
                    params.quotient_dimension,
                    index,
                    params.sweeps,
                    quotient_floor=1.10,
                    null_floor=2.40,
                    offdiag_scale=0.050,
                ),
                projector=skew_projector(
                    params.dimension,
                    params.quotient_dimension,
                    strength=0.08 + 0.005 * index,
                ),
                params=params,
            )
        )
    return rows


def summarize_regime(rows: Sequence[BoundaryRow], name: str) -> RegimeSummary:
    selected = [row for row in rows if row.regime == name]
    if not selected:
        raise ValueError(f"no rows for regime {name}")
    return RegimeSummary(
        name=name,
        kind=selected[0].kind,
        expected_pass=selected[0].expected_pass,
        row_count=len(selected),
        rows_passing=sum(1 for row in selected if row.passed_proxy_checks),
        rows_failing=sum(1 for row in selected if not row.passed_proxy_checks),
        max_projector_symmetry_defect=max(row.projector_symmetry_defect for row in selected),
        max_full_symmetry_defect=max(row.full_symmetry_defect for row in selected),
        max_gauge_null_leakage=max(row.gauge_null_leakage for row in selected),
        min_spectral_margin=min(row.spectral_margin for row in selected),
        classification_matches_expectation=all(
            row.passed_proxy_checks == row.expected_pass for row in selected
        ),
    )


def aggregate_metrics(rows: Sequence[BoundaryRow]) -> dict[str, Any]:
    good = [row for row in rows if row.expected_pass]
    bad = [row for row in rows if not row.expected_pass]
    return {
        "row_count": len(rows),
        "good_row_count": len(good),
        "bad_row_count": len(bad),
        "good_rows_passed": sum(1 for row in good if row.passed_proxy_checks),
        "bad_rows_failed": sum(1 for row in bad if not row.passed_proxy_checks),
        "classification_accuracy": sum(
            1 for row in rows if row.passed_proxy_checks == row.expected_pass
        )
        / float(len(rows)),
        "max_good_symmetry_defect": max(row.full_symmetry_defect for row in good),
        "max_bad_symmetry_defect": max(row.full_symmetry_defect for row in bad),
        "max_good_gauge_null_leakage": max(row.gauge_null_leakage for row in good),
        "max_bad_gauge_null_leakage": max(row.gauge_null_leakage for row in bad),
        "min_good_spectral_margin": min(row.spectral_margin for row in good),
        "min_bad_spectral_margin": min(row.spectral_margin for row in bad),
    }


def build_report(params: Parameters) -> dict[str, Any]:
    rows = build_rows(params)
    summaries = [summarize_regime(rows, name) for name in sorted({row.regime for row in rows})]
    good_regimes = [summary for summary in summaries if summary.expected_pass]
    bad_regimes = [summary for summary in summaries if not summary.expected_pass]
    metrics = aggregate_metrics(rows)
    validation_flags = {
        "all_good_regimes_pass": all(summary.rows_failing == 0 for summary in good_regimes),
        "all_bad_regimes_fail": all(summary.rows_passing == 0 for summary in bad_regimes),
        "classification_matches_expectation": metrics["classification_accuracy"] == 1.0,
        "asymmetric_profile_present": any(row.regime == "asymmetric_boundary_form" for row in rows),
        "gauge_leakage_profile_present": any(
            row.regime == "gauge_null_leaking_boundary" for row in rows
        ),
        "spectral_collapse_profile_present": any(
            row.regime == "induced_ball_spectral_collapse_boundary" for row in rows
        ),
        "nonorthogonal_projection_profile_present": any(
            row.regime == "nonorthogonal_gauge_projection_boundary" for row in rows
        ),
        "stdlib_only": True,
        "deterministic": True,
        "diagnostic_only": True,
        "promotion_blocked": True,
    }
    return {
        "ok": all(validation_flags.values()),
        "promotion": False,
        "diagnostic_only": True,
        "claim_scope": "finite Killing-boundary self-adjointness diagnostic proxy only",
        "parameters": asdict(params),
        "good_regimes": [asdict(summary) for summary in good_regimes],
        "bad_regimes": [asdict(summary) for summary in bad_regimes],
        "aggregate_metrics": metrics,
        "validation_flags": validation_flags,
        "rows": [asdict(row) for row in rows],
        "notes": [
            "Good profiles are symmetric, quotient-stable, orthogonally projected, and gapped.",
            "Bad profiles isolate asymmetry, gauge-null leakage, projection, and spectral-collapse failures.",
            "This receipt is not a YM Hamiltonian domination or continuum mass-gap proof.",
        ],
    }


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    validate_args(args)
    params = Parameters(
        dimension=args.dimension,
        quotient_dimension=args.quotient_dimension,
        sweeps=args.sweeps,
        tolerance=TOLERANCE,
        spectral_margin_floor=0.18,
        leakage_floor=1.0e-9,
    )
    report = build_report(params)
    args.json_output.parent.mkdir(parents=True, exist_ok=True)
    args.json_output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    if args.json:
        print(json.dumps(report, sort_keys=True))
    else:
        print(
            "YM Killing-boundary self-adjointness proxy: "
            f"ok={report['ok']} promotion={report['promotion']} output={args.json_output}"
        )
    return 0 if report["ok"] and not report["promotion"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
