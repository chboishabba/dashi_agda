#!/usr/bin/env python3
"""Finite YM-1 quotient-domain diagnostic.

This pure-stdlib harness models the quotient-domain rung in the YM-1 route:

    gauge-orbit constant mode
    -> weighted projection to the gauge-orthogonal subspace
    -> Hamiltonian action on the quotient domain
    -> symmetry / self-adjointness checks on the quotient matrix

The model is deliberately finite and fail-closed. It does not prove YM-1, any
Hamiltonian theorem, any spectral gap, or any Clay Yang-Mills claim. All
promotion flags remain false.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Sequence


Matrix = list[list[float]]
Vector = list[float]

DEFAULT_OUTPUT = Path("outputs/ym_gauge_quotient_domain_harness.json")


@dataclass(frozen=True)
class HarnessResult:
    nodes: int
    edge_count: int
    weighted_inner_product: str
    gauge_orbit_description: str
    quotient_dimension: int
    projection_idempotence_error: float
    projection_annihilates_constant_error: float
    gauge_orthogonality_error: float
    h_constant_mode_residual: float
    quotient_preservation_error: float
    quotient_symmetry_error: float
    quotient_self_adjoint_error: float
    quotient_matrix_difference_error: float
    sample_rayleigh_quotient: float
    checks: dict[str, bool]
    promotion: bool
    clay_promotion: bool
    ym_1_promotion: bool


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--nodes", type=int, default=6, help="Cycle size; must be >= 3.")
    parser.add_argument("--tolerance", type=float, default=1.0e-10)
    parser.add_argument("--json-output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--json", action="store_true", help="Emit JSON to stdout.")
    parser.add_argument("--quick", action="store_true", help="Accepted for harness uniformity.")
    return parser.parse_args(argv)


def validate_args(args: argparse.Namespace) -> None:
    if args.nodes < 3:
        raise ValueError("--nodes must be at least 3")
    if args.tolerance <= 0.0:
        raise ValueError("--tolerance must be positive")


def zero_matrix(rows: int, cols: int) -> Matrix:
    return [[0.0 for _ in range(cols)] for _ in range(rows)]


def identity_matrix(size: int) -> Matrix:
    matrix = zero_matrix(size, size)
    for i in range(size):
        matrix[i][i] = 1.0
    return matrix


def transpose(matrix: Matrix) -> Matrix:
    if not matrix:
        return []
    return [list(row) for row in zip(*matrix)]


def matmul(left: Matrix, right: Matrix) -> Matrix:
    if not left or not right:
        return []
    right_t = transpose(right)
    return [[sum(a * b for a, b in zip(row, col)) for col in right_t] for row in left]


def matvec(matrix: Matrix, vector: Vector) -> Vector:
    return [sum(a * b for a, b in zip(row, vector)) for row in matrix]


def subtract_matrix(left: Matrix, right: Matrix) -> Matrix:
    return [
        [a - b for a, b in zip(left_row, right_row)]
        for left_row, right_row in zip(left, right)
    ]


def subtract_vector(left: Vector, right: Vector) -> Vector:
    return [a - b for a, b in zip(left, right)]


def max_abs_matrix(matrix: Matrix) -> float:
    return max((abs(value) for row in matrix for value in row), default=0.0)


def max_abs_vector(vector: Vector) -> float:
    return max((abs(value) for value in vector), default=0.0)


def weighted_dot(left: Vector, right: Vector, weights: Vector) -> float:
    return sum(weight * a * b for weight, a, b in zip(weights, left, right))


def weighted_norm_sq(vector: Vector, weights: Vector) -> float:
    return weighted_dot(vector, vector, weights)


def diagonal_inverse(weights: Vector) -> Matrix:
    matrix = zero_matrix(len(weights), len(weights))
    for i, weight in enumerate(weights):
        matrix[i][i] = 1.0 / weight
    return matrix


def weighted_cycle_laplacian(weights: Vector, edge_weights: Vector) -> Matrix:
    nodes = len(weights)
    laplacian = zero_matrix(nodes, nodes)
    for i in range(nodes):
        j = (i + 1) % nodes
        edge_weight = edge_weights[i]
        laplacian[i][i] += edge_weight / weights[i]
        laplacian[i][j] -= edge_weight / weights[i]
        laplacian[j][j] += edge_weight / weights[j]
        laplacian[j][i] -= edge_weight / weights[j]
    return laplacian


def weighted_projection(weights: Vector) -> Matrix:
    nodes = len(weights)
    total_weight = sum(weights)
    projection = zero_matrix(nodes, nodes)
    for i in range(nodes):
        for j in range(nodes):
            delta = 1.0 if i == j else 0.0
            projection[i][j] = delta - weights[j] / total_weight
    return projection


def weighted_qr_basis(weights: Vector) -> Matrix:
    nodes = len(weights)
    constant = [1.0 for _ in range(nodes)]
    basis: list[Vector] = []
    for k in range(nodes - 1):
        candidate = [0.0 for _ in range(nodes)]
        candidate[k] = 1.0
        candidate[k + 1] = -1.0
        for prior in basis:
            coeff = weighted_dot(candidate, prior, weights)
            candidate = [x - coeff * y for x, y in zip(candidate, prior)]
        coeff_constant = weighted_dot(candidate, constant, weights) / weighted_dot(constant, constant, weights)
        candidate = [x - coeff_constant * y for x, y in zip(candidate, constant)]
        norm_sq = weighted_norm_sq(candidate, weights)
        if norm_sq > 1.0e-14:
            scale = norm_sq ** 0.5
            basis.append([x / scale for x in candidate])
    return transpose(basis)


def quotient_matrix(basis: Matrix, hamiltonian: Matrix, weights: Vector) -> Matrix:
    if not basis:
        return []
    nodes = len(weights)
    qdim = len(basis[0])
    result = zero_matrix(qdim, qdim)
    hb = matmul(hamiltonian, basis)
    for i in range(qdim):
        basis_i = [basis[row][i] for row in range(nodes)]
        for j in range(qdim):
            hb_j = [hb[row][j] for row in range(nodes)]
            result[i][j] = weighted_dot(basis_i, hb_j, weights)
    return result


def weighted_symmetry_error(matrix: Matrix, basis_weights: Vector) -> float:
    weighted = [
        [basis_weights[i] * matrix[i][j] for j in range(len(matrix))]
        for i in range(len(matrix))
    ]
    return max_abs_matrix(subtract_matrix(weighted, transpose(weighted)))


def quotient_self_adjoint_error(qmat: Matrix) -> float:
    return max_abs_matrix(subtract_matrix(qmat, transpose(qmat)))


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    validate_args(args)

    nodes = args.nodes
    weights = [1.0 + 0.05 * i for i in range(nodes)]
    edge_weights = [1.0 + 0.07 * i for i in range(nodes)]

    constant_mode = [1.0 for _ in range(nodes)]
    projection = weighted_projection(weights)
    hamiltonian = weighted_cycle_laplacian(weights, edge_weights)
    quotient_basis = weighted_qr_basis(weights)
    quotient_dim = len(quotient_basis[0]) if quotient_basis else 0
    quotient_h = quotient_matrix(quotient_basis, hamiltonian, weights)

    projected_constant = matvec(projection, constant_mode)
    sample = [((3 * i + 2) % 11) / 7.0 - 0.6 for i in range(nodes)]
    projected_sample = matvec(projection, sample)
    projected_twice = matvec(projection, projected_sample)
    h_constant = matvec(hamiltonian, constant_mode)
    h_projected_sample = matvec(hamiltonian, projected_sample)
    projection_after_h = matvec(projection, h_projected_sample)

    basis_t = transpose(quotient_basis)
    gram = zero_matrix(quotient_dim, quotient_dim)
    for i in range(quotient_dim):
        for j in range(quotient_dim):
            gram[i][j] = weighted_dot(basis_t[i], basis_t[j], weights)

    qmat_from_formula = matmul(
        matmul(transpose(quotient_basis), [  # type: ignore[arg-type]
            [weights[i] * hamiltonian[i][j] for j in range(nodes)]
            for i in range(nodes)
        ]),
        quotient_basis,
    )

    gauge_weight_sum = abs(weighted_dot(projected_sample, constant_mode, weights))
    quotient_rayleigh_num = weighted_dot(projected_sample, h_projected_sample, weights)
    quotient_rayleigh_den = weighted_norm_sq(projected_sample, weights)
    sample_rayleigh = quotient_rayleigh_num / quotient_rayleigh_den if quotient_rayleigh_den > 0.0 else 0.0

    result = HarnessResult(
        nodes=nodes,
        edge_count=nodes,
        weighted_inner_product="sum_i w_i x_i y_i",
        gauge_orbit_description="constant scalar mode on finite weighted cycle",
        quotient_dimension=quotient_dim,
        projection_idempotence_error=max_abs_vector(subtract_vector(projected_twice, projected_sample)),
        projection_annihilates_constant_error=max_abs_vector(projected_constant),
        gauge_orthogonality_error=gauge_weight_sum,
        h_constant_mode_residual=max_abs_vector(h_constant),
        quotient_preservation_error=max_abs_vector(subtract_vector(projection_after_h, h_projected_sample)),
        quotient_symmetry_error=weighted_symmetry_error(hamiltonian, weights),
        quotient_self_adjoint_error=quotient_self_adjoint_error(quotient_h),
        quotient_matrix_difference_error=max_abs_matrix(subtract_matrix(gram, identity_matrix(quotient_dim))),
        sample_rayleigh_quotient=sample_rayleigh,
        checks={},
        promotion=False,
        clay_promotion=False,
        ym_1_promotion=False,
    )

    checks = {
        "projection_is_idempotent": result.projection_idempotence_error <= args.tolerance,
        "projection_kills_constant_mode": result.projection_annihilates_constant_error <= args.tolerance,
        "projected_sample_is_gauge_orthogonal": result.gauge_orthogonality_error <= args.tolerance,
        "hamiltonian_kills_constant_mode": result.h_constant_mode_residual <= args.tolerance,
        "hamiltonian_preserves_quotient_domain": result.quotient_preservation_error <= args.tolerance,
        "hamiltonian_is_weighted_symmetric": result.quotient_symmetry_error <= args.tolerance,
        "quotient_matrix_is_self_adjoint": result.quotient_self_adjoint_error <= args.tolerance,
        "quotient_basis_is_weighted_orthonormal": result.quotient_matrix_difference_error <= 1.0e-9,
        "sample_rayleigh_is_nonnegative": result.sample_rayleigh_quotient >= -args.tolerance,
        "promotion_false": (not result.promotion and not result.clay_promotion and not result.ym_1_promotion),
    }

    payload: dict[str, Any] = {
        "contract": "YM gauge quotient domain diagnostic",
        "result": asdict(HarnessResult(**{**asdict(result), "checks": checks})),
        "orcf": {
            "O": "single-file pure-stdlib harness for the YM-1 quotient-domain rung",
            "R": "model gauge constant mode, gauge-orthogonal projection, quotient-domain preservation, and quotient self-adjointness",
            "C": "scripts/ym_gauge_quotient_domain_harness.py",
            "S": "finite weighted cycle model only; no theorem promotion",
            "L": "diagnostic harness -> local validation -> possible repo integration; no Clay/YM proof authority",
            "P": "weighted projection plus finite Hamiltonian on quotient basis",
            "G": "promotion=false always; this artifact cannot certify YM-1, spectral gap, or Clay Yang-Mills",
            "F": "missing analytic boundary proof, domain closure proof, full Hodge/gauge quotient proof, and continuum transfer",
        },
        "promotion": {
            "promotion": False,
            "clay_promotion": False,
            "ym_1_promotion": False,
        },
    }

    if args.json_output:
        args.json_output.parent.mkdir(parents=True, exist_ok=True)
        with args.json_output.open("w", encoding="utf-8") as handle:
            json.dump(payload, handle, indent=2, sort_keys=True)
            handle.write("\n")

    if args.json:
        print(json.dumps(payload, indent=2, sort_keys=True))
    else:
        print(f"projection_is_idempotent={checks['projection_is_idempotent']}")
        print(f"hamiltonian_preserves_quotient_domain={checks['hamiltonian_preserves_quotient_domain']}")
        print(f"quotient_matrix_is_self_adjoint={checks['quotient_matrix_is_self_adjoint']}")
        print("promotion=false")
    return 0 if all(checks.values()) else 1


if __name__ == "__main__":
    raise SystemExit(main())
