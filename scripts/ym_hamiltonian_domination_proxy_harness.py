#!/usr/bin/env python3
"""Finite matrix proxy for YM Hamiltonian domination on a quotient subspace.

This pure-stdlib diagnostic checks small deterministic matrix cases for the
formal domination inequality

    H >= c1 * Delta + c2 * Hol - E

after projection to a finite quotient subspace.  It is only a proxy harness:
it does not prove Yang-Mills Hamiltonian domination, continuum transfer,
holonomy control, mass gap, or any Clay statement.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Sequence


Matrix = list[list[float]]

DEFAULT_OUTPUT = Path("outputs/ym_hamiltonian_domination_proxy_harness.json")


@dataclass(frozen=True)
class Constants:
    c1: float
    c2: float
    energy_shift: float
    tolerance: float
    holonomy_floor: float
    near_zero_floor: float


@dataclass(frozen=True)
class CaseSummary:
    name: str
    description: str
    expected_pass: bool
    passed_proxy_checks: bool
    dimension: int
    quotient_dimension: int
    domination_margin: float
    h_min_eigenvalue: float
    delta_min_eigenvalue: float
    hol_min_eigenvalue: float
    comparison_min_eigenvalue: float
    quotient_commutator_error: float
    max_symmetry_error: float
    holonomy_controlled: bool
    near_zero_h_sector: bool
    eigenvalue_margins: dict[str, Any]
    checks: dict[str, bool]
    failure_reasons: list[str]


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dimension", type=int, default=5)
    parser.add_argument("--quotient-dimension", type=int, default=3)
    parser.add_argument("--c1", type=float, default=0.6)
    parser.add_argument("--c2", type=float, default=0.8)
    parser.add_argument("--energy-shift", type=float, default=0.05)
    parser.add_argument("--tolerance", type=float, default=1.0e-9)
    parser.add_argument("--holonomy-floor", type=float, default=0.05)
    parser.add_argument("--near-zero-floor", type=float, default=0.05)
    parser.add_argument("--jacobi-sweeps", type=int, default=80)
    parser.add_argument("--json-output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--json", action="store_true", help="Emit compact JSON to stdout.")
    return parser.parse_args(argv)


def validate_args(args: argparse.Namespace) -> None:
    if args.dimension < 3:
        raise ValueError("--dimension must be at least 3")
    if not (1 <= args.quotient_dimension < args.dimension):
        raise ValueError("--quotient-dimension must be between 1 and dimension - 1")
    if args.c1 < 0.0 or args.c2 < 0.0:
        raise ValueError("--c1 and --c2 must be nonnegative")
    if args.energy_shift < 0.0:
        raise ValueError("--energy-shift must be nonnegative")
    if args.tolerance <= 0.0:
        raise ValueError("--tolerance must be positive")
    if args.holonomy_floor <= 0.0:
        raise ValueError("--holonomy-floor must be positive")
    if args.near_zero_floor <= 0.0:
        raise ValueError("--near-zero-floor must be positive")
    if args.jacobi_sweeps <= 0:
        raise ValueError("--jacobi-sweeps must be positive")


def zero_matrix(rows: int, cols: int) -> Matrix:
    return [[0.0 for _ in range(cols)] for _ in range(rows)]


def diagonal(values: Sequence[float], dimension: int) -> Matrix:
    matrix = zero_matrix(dimension, dimension)
    for index, value in enumerate(values[:dimension]):
        matrix[index][index] = value
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


def symmetry_error(matrix: Matrix) -> float:
    return max_abs(sub(matrix, transpose(matrix)))


def commutator_error(matrix: Matrix, projector: Matrix) -> float:
    return max_abs(sub(matmul(matrix, projector), matmul(projector, matrix)))


def quotient_block(matrix: Matrix, quotient_dimension: int) -> Matrix:
    return [row[:quotient_dimension] for row in matrix[:quotient_dimension]]


def jacobi_eigenvalues_symmetric(matrix: Matrix, sweeps: int, tolerance: float) -> list[float]:
    """Return eigenvalues for a small real symmetric matrix using Jacobi sweeps."""
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


def pad_diagonal(quotient_values: Sequence[float], dimension: int, tail_value: float) -> Matrix:
    values = list(quotient_values)
    values.extend(tail_value + 0.2 * index for index in range(dimension - len(values)))
    return diagonal(values, dimension)


def base_delta(dimension: int, quotient_dimension: int) -> Matrix:
    return pad_diagonal([1.0 + index for index in range(quotient_dimension)], dimension, 4.5)


def base_holonomy(dimension: int, quotient_dimension: int, weak_first: bool) -> Matrix:
    values = [0.4 + 0.5 * index for index in range(quotient_dimension)]
    if weak_first:
        values[0] = 1.0e-8
    return pad_diagonal(values, dimension, 2.5)


def comparison_operator(delta: Matrix, hol: Matrix, constants: Constants) -> Matrix:
    dim = len(delta)
    return sub(add(scale(constants.c1, delta), scale(constants.c2, hol)), scale(constants.energy_shift, identity(dim)))


def good_hamiltonian(delta: Matrix, hol: Matrix, constants: Constants) -> Matrix:
    h = add(comparison_operator(delta, hol, constants), diagonal([0.32, 0.45, 0.7, 1.0, 1.2], len(delta)))
    if len(h) >= 3:
        h[0][1] = 0.03
        h[1][0] = 0.03
        h[1][2] = -0.02
        h[2][1] = -0.02
    return h


def weak_hamiltonian(delta: Matrix, hol: Matrix, constants: Constants) -> Matrix:
    h = good_hamiltonian(delta, hol, constants)
    if len(h) >= 2:
        h[1][1] -= 0.8
    return h


def near_zero_sector_hamiltonian(delta: Matrix, hol: Matrix, constants: Constants) -> Matrix:
    h = good_hamiltonian(delta, hol, constants)
    h[0][0] = 0.02
    h[0][1] = 0.0
    h[1][0] = 0.0
    return h


def min_eigenvalue(matrix: Matrix, sweeps: int, tolerance: float) -> float:
    values = jacobi_eigenvalues_symmetric(matrix, sweeps, tolerance)
    return min(values) if values else 0.0


def summarize_case(
    *,
    name: str,
    description: str,
    expected_pass: bool,
    hamiltonian: Matrix,
    delta: Matrix,
    hol: Matrix,
    projector: Matrix,
    quotient_dimension: int,
    constants: Constants,
    jacobi_sweeps: int,
) -> CaseSummary:
    hq = quotient_block(hamiltonian, quotient_dimension)
    dq = quotient_block(delta, quotient_dimension)
    holq = quotient_block(hol, quotient_dimension)
    comparison = comparison_operator(delta, hol, constants)
    cq = quotient_block(comparison, quotient_dimension)
    domination = sub(hq, cq)

    h_sym = symmetry_error(hamiltonian)
    delta_sym = symmetry_error(delta)
    hol_sym = symmetry_error(hol)
    comm_errors = [
        commutator_error(matrix, projector) for matrix in (hamiltonian, delta, hol)
    ]
    max_comm = max(comm_errors, default=0.0)

    h_min = min_eigenvalue(hq, jacobi_sweeps, constants.tolerance)
    delta_min = min_eigenvalue(dq, jacobi_sweeps, constants.tolerance)
    hol_min = min_eigenvalue(holq, jacobi_sweeps, constants.tolerance)
    comparison_min = min_eigenvalue(cq, jacobi_sweeps, constants.tolerance)
    domination_values = jacobi_eigenvalues_symmetric(
        domination, jacobi_sweeps, constants.tolerance
    )
    domination_margin = min(domination_values) if domination_values else 0.0

    symmetric = max(h_sym, delta_sym, hol_sym) <= constants.tolerance
    quotient_stable = max_comm <= constants.tolerance
    dominated = domination_margin >= -constants.tolerance
    holonomy_controlled = hol_min >= constants.holonomy_floor
    near_zero_h_sector = h_min < constants.near_zero_floor
    no_uncontrolled_near_zero = holonomy_controlled or not near_zero_h_sector
    passed = symmetric and quotient_stable and dominated and no_uncontrolled_near_zero
    checks = {
        "symmetric_forms": symmetric,
        "quotient_stable": quotient_stable,
        "domination_psd_margin": dominated,
        "holonomy_controlled_or_no_near_zero_h_sector": no_uncontrolled_near_zero,
    }
    failure_reasons = [key for key, value in checks.items() if not value]

    return CaseSummary(
        name=name,
        description=description,
        expected_pass=expected_pass,
        passed_proxy_checks=passed,
        dimension=len(hamiltonian),
        quotient_dimension=quotient_dimension,
        domination_margin=domination_margin,
        h_min_eigenvalue=h_min,
        delta_min_eigenvalue=delta_min,
        hol_min_eigenvalue=hol_min,
        comparison_min_eigenvalue=comparison_min,
        quotient_commutator_error=max_comm,
        max_symmetry_error=max(h_sym, delta_sym, hol_sym),
        holonomy_controlled=holonomy_controlled,
        near_zero_h_sector=near_zero_h_sector,
        eigenvalue_margins={
            "domination_eigenvalues": domination_values,
            "h_minus_comparison_min": domination_margin,
            "h_min_minus_comparison_min": h_min - comparison_min,
            "h_min": h_min,
            "comparison_min": comparison_min,
            "hol_min": hol_min,
            "delta_min": delta_min,
        },
        checks=checks,
        failure_reasons=failure_reasons,
    )


def build_summary(args: argparse.Namespace) -> dict[str, Any]:
    validate_args(args)
    constants = Constants(
        c1=args.c1,
        c2=args.c2,
        energy_shift=args.energy_shift,
        tolerance=args.tolerance,
        holonomy_floor=args.holonomy_floor,
        near_zero_floor=args.near_zero_floor,
    )
    projector = identity_projector(args.dimension, args.quotient_dimension)

    strong_delta = base_delta(args.dimension, args.quotient_dimension)
    strong_hol = base_holonomy(args.dimension, args.quotient_dimension, weak_first=False)
    weak_hol = base_holonomy(args.dimension, args.quotient_dimension, weak_first=True)

    cases = [
        summarize_case(
            name="good_psd_dominated",
            description="PSD surplus over c1*Delta + c2*Hol - E on the quotient; expected to pass.",
            expected_pass=True,
            hamiltonian=good_hamiltonian(strong_delta, strong_hol, constants),
            delta=strong_delta,
            hol=strong_hol,
            projector=projector,
            quotient_dimension=args.quotient_dimension,
            constants=constants,
            jacobi_sweeps=args.jacobi_sweeps,
        ),
        summarize_case(
            name="bad_weak_h",
            description="Hamiltonian weakened in one quotient direction so H - comparison has a negative eigenvalue.",
            expected_pass=False,
            hamiltonian=weak_hamiltonian(strong_delta, strong_hol, constants),
            delta=strong_delta,
            hol=strong_hol,
            projector=projector,
            quotient_dimension=args.quotient_dimension,
            constants=constants,
            jacobi_sweeps=args.jacobi_sweeps,
        ),
        summarize_case(
            name="bad_non_holonomy_controlled_near_zero",
            description="Near-zero Hamiltonian direction with tiny holonomy floor; expected to fail control and domination.",
            expected_pass=False,
            hamiltonian=near_zero_sector_hamiltonian(strong_delta, weak_hol, constants),
            delta=strong_delta,
            hol=weak_hol,
            projector=projector,
            quotient_dimension=args.quotient_dimension,
            constants=constants,
            jacobi_sweeps=args.jacobi_sweeps,
        ),
    ]

    case_dicts = [asdict(case) for case in cases]
    good_flags = {
        case.name: case.passed_proxy_checks for case in cases if case.expected_pass
    }
    bad_flags = {
        case.name: not case.passed_proxy_checks for case in cases if not case.expected_pass
    }
    checks = {
        "good_cases_pass": all(good_flags.values()),
        "bad_cases_fail": all(bad_flags.values()),
        "weak_h_case_fails": bad_flags.get("bad_weak_h", False),
        "non_holonomy_controlled_near_zero_sector_fails": bad_flags.get(
            "bad_non_holonomy_controlled_near_zero", False
        ),
        "promotion_false": True,
    }
    return {
        "harness": "ym_hamiltonian_domination_proxy",
        "version": 1,
        "claim_scope": "finite quotient matrix diagnostic proxy only",
        "ok": all(checks.values()),
        "promotion": False,
        "dimension": args.dimension,
        "quotient_dimension": args.quotient_dimension,
        "constants": asdict(constants),
        "jacobi_sweeps": args.jacobi_sweeps,
        "cases": case_dicts,
        "eigenvalue_margins": {
            case.name: case.eigenvalue_margins for case in cases
        },
        "validation_flags": {
            "good": good_flags,
            "bad": bad_flags,
        },
        "checks": checks,
        "notes": [
            "All operators are deterministic finite real symmetric matrices.",
            "The quotient is modeled by the leading coordinate projector.",
            "Passing this harness is not promotion and does not establish continuum YM domination.",
        ],
    }


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    summary = build_summary(args)
    args.json_output.parent.mkdir(parents=True, exist_ok=True)
    args.json_output.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
    if args.json:
        print(json.dumps(summary, sort_keys=True))
    else:
        print(
            json.dumps(
                {
                    "ok": summary["ok"],
                    "promotion": summary["promotion"],
                    "json_output": str(args.json_output),
                    "validation_flags": summary["validation_flags"],
                },
                sort_keys=True,
            )
        )
    return 0 if summary["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
