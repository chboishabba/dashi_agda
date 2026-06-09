#!/usr/bin/env python3
"""Finite YM self-adjoint Hamiltonian proxy harness.

This pure-stdlib diagnostic models the finite operator-theoretic gate recorded
by ``YMSelfAdjointFiniteHamiltonianBoundary``:

    finite domain + symmetric form + gauge quotient projection
    -> self-adjoint finite Hamiltonian with discrete spectrum proxy.

The harness compares three deterministic small matrix cases:

* ``symmetric_quotient_stable``: symmetric matrix preserving the quotient
  subspace, expected to pass.
* ``bad_nonsymmetric``: domain-stable but nonsymmetric matrix, expected to
  fail self-adjointness.
* ``bad_domain_unstable``: symmetric full matrix that does not commute with
  the quotient projector, expected to fail quotient descent.

It emits JSON and always keeps ``promotion=false``.  This is not a proof of
Yang-Mills Hamiltonian self-adjointness, Hamiltonian domination, OS transfer,
continuum transfer, or Clay Yang-Mills.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Sequence


Matrix = list[list[float]]
Vector = list[float]

DEFAULT_OUTPUT = Path("outputs/ym_finite_selfadjoint_hamiltonian_proxy_harness.json")


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
    quotient_commutator_error: float
    quotient_matrix_symmetry_error: float
    eigenvalues: list[float]
    eigenvalue_count: int
    spectral_diameter: float
    min_positive_gap: float | None
    checks: dict[str, bool]
    failure_reasons: list[str]


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dimension", type=int, default=6)
    parser.add_argument("--quotient-dimension", type=int, default=4)
    parser.add_argument("--tolerance", type=float, default=1.0e-9)
    parser.add_argument("--jacobi-sweeps", type=int, default=80)
    parser.add_argument("--json-output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--json", action="store_true", help="Emit compact JSON to stdout.")
    return parser.parse_args(argv)


def validate_args(args: argparse.Namespace) -> None:
    if args.dimension < 3:
        raise ValueError("--dimension must be at least 3")
    if not (1 <= args.quotient_dimension < args.dimension):
        raise ValueError("--quotient-dimension must be between 1 and dimension - 1")
    if args.tolerance <= 0.0:
        raise ValueError("--tolerance must be positive")
    if args.jacobi_sweeps <= 0:
        raise ValueError("--jacobi-sweeps must be positive")


def zero_matrix(rows: int, cols: int) -> Matrix:
    return [[0.0 for _ in range(cols)] for _ in range(rows)]


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


def sub(left: Matrix, right: Matrix) -> Matrix:
    return [
        [a - b for a, b in zip(left_row, right_row)]
        for left_row, right_row in zip(left, right)
    ]


def max_abs(matrix: Matrix) -> float:
    return max((abs(value) for row in matrix for value in row), default=0.0)


def symmetry_error(matrix: Matrix) -> float:
    return max_abs(sub(matrix, transpose(matrix)))


def commutator_error(matrix: Matrix, projector: Matrix) -> float:
    return max_abs(sub(matmul(matrix, projector), matmul(projector, matrix)))


def quotient_block(matrix: Matrix, quotient_dimension: int) -> Matrix:
    return [row[:quotient_dimension] for row in matrix[:quotient_dimension]]


def sorted_eigen_gaps(eigenvalues: Sequence[float], tolerance: float) -> tuple[float, float | None]:
    if not eigenvalues:
        return 0.0, None
    ordered = sorted(eigenvalues)
    diameter = ordered[-1] - ordered[0]
    positive_gaps = [
        ordered[index + 1] - ordered[index]
        for index in range(len(ordered) - 1)
        if ordered[index + 1] - ordered[index] > tolerance
    ]
    return diameter, min(positive_gaps) if positive_gaps else None


def jacobi_eigenvalues_symmetric(matrix: Matrix, sweeps: int, tolerance: float) -> list[float]:
    """Return eigenvalues for a small real symmetric matrix using Jacobi sweeps."""
    n = len(matrix)
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

        app = a[p][p]
        aqq = a[q][q]
        apq = a[p][q]
        if abs(apq) <= tolerance:
            continue
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


def symmetric_quotient_stable_matrix(dimension: int, quotient_dimension: int) -> Matrix:
    matrix = zero_matrix(dimension, dimension)
    for i in range(dimension):
        for j in range(i, dimension):
            same_block = (i < quotient_dimension and j < quotient_dimension) or (
                i >= quotient_dimension and j >= quotient_dimension
            )
            if not same_block:
                value = 0.0
            elif i == j:
                value = 2.0 + 0.37 * (i + 1)
            else:
                value = 0.08 * ((i + 1) + (j + 1)) / float(dimension)
            matrix[i][j] = value
            matrix[j][i] = value
    return matrix


def bad_nonsymmetric_matrix(dimension: int, quotient_dimension: int) -> Matrix:
    matrix = symmetric_quotient_stable_matrix(dimension, quotient_dimension)
    if quotient_dimension >= 2:
        matrix[0][1] += 0.65
    else:
        matrix[0][0] += 0.0
    return matrix


def bad_domain_unstable_matrix(dimension: int, quotient_dimension: int) -> Matrix:
    matrix = symmetric_quotient_stable_matrix(dimension, quotient_dimension)
    outside = quotient_dimension
    for i in range(quotient_dimension):
        coupling = 0.22 + 0.03 * i
        matrix[i][outside] = coupling
        matrix[outside][i] = coupling
    return matrix


def summarize_case(
    *,
    name: str,
    description: str,
    expected_pass: bool,
    matrix: Matrix,
    projector: Matrix,
    quotient_dimension: int,
    tolerance: float,
    jacobi_sweeps: int,
) -> CaseSummary:
    dimension = len(matrix)
    p2_error = max_abs(sub(matmul(projector, projector), projector))
    p_sym_error = symmetry_error(projector)
    h_sym_error = symmetry_error(matrix)
    comm_error = commutator_error(matrix, projector)
    q_matrix = quotient_block(matmul(matmul(projector, matrix), projector), quotient_dimension)
    q_sym_error = symmetry_error(q_matrix)

    projector_ok = p2_error <= tolerance and p_sym_error <= tolerance
    symmetric_ok = h_sym_error <= tolerance
    quotient_stable_ok = comm_error <= tolerance
    quotient_symmetric_ok = q_sym_error <= tolerance
    finite_discrete_proxy_ok = symmetric_ok and quotient_stable_ok and quotient_symmetric_ok

    if quotient_symmetric_ok:
        eigenvalues = jacobi_eigenvalues_symmetric(q_matrix, jacobi_sweeps, tolerance)
    else:
        eigenvalues = []
    spectral_diameter, min_positive_gap = sorted_eigen_gaps(eigenvalues, tolerance)
    spectrum_count_ok = len(eigenvalues) == quotient_dimension
    spectrum_real_proxy_ok = bool(eigenvalues) and all(math.isfinite(x) for x in eigenvalues)

    checks = {
        "orthogonal_projector": projector_ok,
        "finite_form_symmetric": symmetric_ok,
        "quotient_domain_stable": quotient_stable_ok,
        "quotient_matrix_symmetric": quotient_symmetric_ok,
        "finite_discrete_spectrum_proxy": finite_discrete_proxy_ok
        and spectrum_count_ok
        and spectrum_real_proxy_ok,
    }
    passed = all(checks.values())
    failure_reasons = [key for key, value in checks.items() if not value]
    return CaseSummary(
        name=name,
        description=description,
        expected_pass=expected_pass,
        passed_proxy_checks=passed,
        dimension=dimension,
        quotient_dimension=quotient_dimension,
        max_symmetry_error=h_sym_error,
        projector_idempotence_error=p2_error,
        projector_symmetry_error=p_sym_error,
        quotient_commutator_error=comm_error,
        quotient_matrix_symmetry_error=q_sym_error,
        eigenvalues=eigenvalues,
        eigenvalue_count=len(eigenvalues),
        spectral_diameter=spectral_diameter,
        min_positive_gap=min_positive_gap,
        checks=checks,
        failure_reasons=failure_reasons,
    )


def build_summary(args: argparse.Namespace) -> dict[str, Any]:
    validate_args(args)
    projector = identity_projector(args.dimension, args.quotient_dimension)
    cases = [
        summarize_case(
            name="symmetric_quotient_stable",
            description=(
                "Symmetric block-preserving finite Hamiltonian proxy; "
                "expected to descend to the quotient."
            ),
            expected_pass=True,
            matrix=symmetric_quotient_stable_matrix(args.dimension, args.quotient_dimension),
            projector=projector,
            quotient_dimension=args.quotient_dimension,
            tolerance=args.tolerance,
            jacobi_sweeps=args.jacobi_sweeps,
        ),
        summarize_case(
            name="bad_nonsymmetric",
            description=(
                "Domain-stable matrix with an asymmetric quotient block; "
                "expected to fail finite-form self-adjointness."
            ),
            expected_pass=False,
            matrix=bad_nonsymmetric_matrix(args.dimension, args.quotient_dimension),
            projector=projector,
            quotient_dimension=args.quotient_dimension,
            tolerance=args.tolerance,
            jacobi_sweeps=args.jacobi_sweeps,
        ),
        summarize_case(
            name="bad_domain_unstable",
            description=(
                "Symmetric full matrix with off-block coupling; expected to "
                "fail quotient/domain stability because [H,P] is nonzero."
            ),
            expected_pass=False,
            matrix=bad_domain_unstable_matrix(args.dimension, args.quotient_dimension),
            projector=projector,
            quotient_dimension=args.quotient_dimension,
            tolerance=args.tolerance,
            jacobi_sweeps=args.jacobi_sweeps,
        ),
    ]
    good_cases = [case for case in cases if case.expected_pass]
    bad_cases = [case for case in cases if not case.expected_pass]
    expected_behavior_ok = all(case.passed_proxy_checks for case in good_cases) and all(
        not case.passed_proxy_checks for case in bad_cases
    )
    output = {
        "harness": "ym_finite_selfadjoint_hamiltonian_proxy",
        "version": 1,
        "promotion": False,
        "claim_scope": "finite diagnostic proxy only",
        "dimension": args.dimension,
        "quotient_dimension": args.quotient_dimension,
        "tolerance": args.tolerance,
        "jacobi_sweeps": args.jacobi_sweeps,
        "cases": [asdict(case) for case in cases],
        "checks": {
            "good_symmetric_case_passes": all(case.passed_proxy_checks for case in good_cases),
            "bad_cases_fail_visibly": all(not case.passed_proxy_checks for case in bad_cases),
            "nonsymmetric_case_detected": any(
                case.name == "bad_nonsymmetric"
                and "finite_form_symmetric" in case.failure_reasons
                for case in bad_cases
            ),
            "domain_unstable_case_detected": any(
                case.name == "bad_domain_unstable"
                and "quotient_domain_stable" in case.failure_reasons
                for case in bad_cases
            ),
            "promotion_false": True,
        },
        "ok": expected_behavior_ok,
        "notes": [
            "Jacobi eigenvalues are computed only for symmetric quotient blocks.",
            "Finite spectrum here means a finite-dimensional matrix spectrum proxy.",
            "This does not prove gauge quotient construction or YM Hamiltonian domination.",
        ],
    }
    output["checks"]["expected_behavior_ok"] = expected_behavior_ok
    return output


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    summary = build_summary(args)
    args.json_output.parent.mkdir(parents=True, exist_ok=True)
    args.json_output.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
    if args.json:
        print(json.dumps(summary, sort_keys=True))
    else:
        print(
            "ym_finite_selfadjoint_hamiltonian_proxy: "
            f"ok={summary['ok']} promotion={summary['promotion']} "
            f"output={args.json_output}"
        )
    return 0 if summary["ok"] and not summary["promotion"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
