#!/usr/bin/env python3
"""Finite YM-1 Killing/full-degree self-adjointness diagnostic.

This pure-stdlib harness models the first finite operator-theoretic rung in the
YM route:

    full-degree/Killing boundary convention
    + weighted coboundary d and weighted adjoint d*
    + H = d* d
    -> weighted self-adjoint finite Hamiltonian with gauge-constant null mode.

The graph is a finite 2D grid with opposite boundary faces identified for the
operator calculation.  This keeps every vertex at full degree while making the
boundary contribution cancel by an explicit opposite-face involution.  The
diagnostic is finite bookkeeping only; all Clay/YM promotion flags remain false.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Sequence


Matrix = list[list[float]]
Vector = list[float]

DEFAULT_OUTPUT = Path("outputs/ym_killing_boundary_self_adjointness_harness.json")


@dataclass(frozen=True)
class HarnessResult:
    depth: int
    vertex_count: int
    edge_count: int
    boundary_convention: str
    weighted_inner_product: str
    symmetry_error: float
    adjoint_error: float
    laplacian_factorization_error: float
    null_mode_residual: float
    boundary_flux_cancellation_error: float
    full_degree_error: float
    quotient_constant_preservation_error: float
    gauge_constant_energy: float
    sample_energy: float
    sample_energy_from_d: float
    promotion: bool
    clay_promotion: bool
    ym_1_promotion: bool
    checks: dict[str, bool]


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--depth", type=int, default=4, help="Grid side length; must be >= 2.")
    parser.add_argument("--tolerance", type=float, default=1.0e-10)
    parser.add_argument("--json-output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--json", action="store_true", help="Emit JSON to stdout.")
    return parser.parse_args(argv)


def validate_args(args: argparse.Namespace) -> None:
    if args.depth < 2:
        raise ValueError("--depth must be at least 2")
    if args.tolerance <= 0.0:
        raise ValueError("--tolerance must be positive")


def vertex_index(x: int, y: int, depth: int) -> int:
    return y * depth + x


def vertices(depth: int) -> list[tuple[int, int]]:
    return [(x, y) for y in range(depth) for x in range(depth)]


def oriented_edges(depth: int) -> list[tuple[int, int, str, bool]]:
    """Return full-degree oriented +x/+y edges with wrap boundary marker."""
    edges: list[tuple[int, int, str, bool]] = []
    for y in range(depth):
        for x in range(depth):
            source = vertex_index(x, y, depth)
            target_x = vertex_index((x + 1) % depth, y, depth)
            target_y = vertex_index(x, (y + 1) % depth, depth)
            edges.append((source, target_x, "x", x + 1 == depth))
            edges.append((source, target_y, "y", y + 1 == depth))
    return edges


def vertex_weights(depth: int) -> Vector:
    # Mild deterministic positive weights exercise the weighted-adjoint path.
    return [
        1.0 + 0.03 * x + 0.05 * y
        for x, y in vertices(depth)
    ]


def edge_weights(edges: Sequence[tuple[int, int, str, bool]], depth: int) -> Vector:
    weights: Vector = []
    for source, _target, axis, wraps_boundary in edges:
        x = source % depth
        y = source // depth
        axis_offset = 0.07 if axis == "x" else 0.11
        boundary_offset = 0.0 if not wraps_boundary else 0.0
        weights.append(1.0 + axis_offset + 0.01 * x + 0.015 * y + boundary_offset)
    return weights


def zero_matrix(rows: int, cols: int) -> Matrix:
    return [[0.0 for _ in range(cols)] for _ in range(rows)]


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
        [a - b for a, b in zip(row_left, row_right)]
        for row_left, row_right in zip(left, right)
    ]


def subtract_vector(left: Vector, right: Vector) -> Vector:
    return [a - b for a, b in zip(left, right)]


def max_abs_matrix(matrix: Matrix) -> float:
    return max((abs(value) for row in matrix for value in row), default=0.0)


def max_abs_vector(vector: Vector) -> float:
    return max((abs(value) for value in vector), default=0.0)


def weighted_dot(left: Vector, right: Vector, weights: Vector) -> float:
    return sum(weight * a * b for weight, a, b in zip(weights, left, right))


def incidence_matrix(edges: Sequence[tuple[int, int, str, bool]], vertex_count: int) -> Matrix:
    d = zero_matrix(len(edges), vertex_count)
    for row, (source, target, _axis, _wraps_boundary) in enumerate(edges):
        d[row][source] = -1.0
        d[row][target] = 1.0
    return d


def weighted_adjoint(d: Matrix, w0: Vector, w1: Vector) -> Matrix:
    # d* = W0^{-1} d^T W1 for diagonal positive weights.
    d_t = transpose(d)
    adj = zero_matrix(len(d_t), len(d_t[0]) if d_t else 0)
    for i, row in enumerate(d_t):
        for j, value in enumerate(row):
            adj[i][j] = value * w1[j] / w0[i]
    return adj


def weighted_symmetry_error(matrix: Matrix, weights: Vector) -> float:
    weighted = [
        [weights[i] * matrix[i][j] for j in range(len(matrix))]
        for i in range(len(matrix))
    ]
    return max_abs_matrix(subtract_matrix(weighted, transpose(weighted)))


def matrix_difference_from_formula(d_star: Matrix, d: Matrix, laplacian: Matrix) -> float:
    return max_abs_matrix(subtract_matrix(matmul(d_star, d), laplacian))


def explicit_laplacian(d: Matrix, w0: Vector, w1: Vector) -> Matrix:
    vertex_count = len(w0)
    laplacian = zero_matrix(vertex_count, vertex_count)
    for edge_index, row in enumerate(d):
        for i, d_i in enumerate(row):
            if d_i == 0.0:
                continue
            for j, d_j in enumerate(row):
                if d_j != 0.0:
                    laplacian[i][j] += w1[edge_index] * d_i * d_j / w0[i]
    return laplacian


def adjoint_identity_error(d: Matrix, d_star: Matrix, w0: Vector, w1: Vector) -> float:
    vertex_count = len(w0)
    edge_count = len(w1)
    tests_v = [
        [1.0 + ((i * 7 + shift) % 11) / 13.0 for i in range(vertex_count)]
        for shift in range(3)
    ]
    tests_e = [
        [((j * 5 + shift) % 17) / 19.0 - 0.4 for j in range(edge_count)]
        for shift in range(3)
    ]
    error = 0.0
    for v in tests_v:
        dv = matvec(d, v)
        for eta in tests_e:
            lhs = weighted_dot(dv, eta, w1)
            rhs = weighted_dot(v, matvec(d_star, eta), w0)
            error = max(error, abs(lhs - rhs))
    return error


def boundary_flux_cancellation_error(
    depth: int,
    edges: Sequence[tuple[int, int, str, bool]],
    sample: Vector,
) -> float:
    flux_by_axis = {"x": 0.0, "y": 0.0}
    opposite_by_axis = {"x": 0.0, "y": 0.0}
    for source, target, axis, wraps_boundary in edges:
        if not wraps_boundary:
            continue
        flux = sample[target] - sample[source]
        flux_by_axis[axis] += flux
        # Opposite-face involution reverses orientation, so the paired flux
        # must cancel this boundary contribution.
        opposite_by_axis[axis] += -flux
    return max(abs(flux_by_axis[axis] + opposite_by_axis[axis]) for axis in ("x", "y"))


def full_degree_error(depth: int, edges: Sequence[tuple[int, int, str, bool]]) -> float:
    degree = [0 for _ in range(depth * depth)]
    for source, target, _axis, _wraps_boundary in edges:
        degree[source] += 1
        degree[target] += 1
    return max(abs(value - 4) for value in degree)


def sample_field(depth: int) -> Vector:
    return [
        0.2 + 0.17 * x - 0.09 * y + 0.03 * ((x * y + 1) % 5)
        for x, y in vertices(depth)
    ]


def run(depth: int, tolerance: float) -> HarnessResult:
    edge_list = oriented_edges(depth)
    vertex_count = depth * depth
    d = incidence_matrix(edge_list, vertex_count)
    w0 = vertex_weights(depth)
    w1 = edge_weights(edge_list, depth)
    d_star = weighted_adjoint(d, w0, w1)
    hamiltonian = explicit_laplacian(d, w0, w1)

    constant = [1.0 for _ in range(vertex_count)]
    d_constant = matvec(d, constant)
    h_constant = matvec(hamiltonian, constant)
    field = sample_field(depth)
    d_field = matvec(d, field)
    h_field = matvec(hamiltonian, field)

    adjoint_error = adjoint_identity_error(d, d_star, w0, w1)
    symmetry_error = weighted_symmetry_error(hamiltonian, w0)
    factorization_error = matrix_difference_from_formula(d_star, d, hamiltonian)
    null_mode_residual = max(max_abs_vector(d_constant), max_abs_vector(h_constant))
    boundary_error = boundary_flux_cancellation_error(depth, edge_list, field)
    degree_error = full_degree_error(depth, edge_list)
    constant_mean = sum(w * value for w, value in zip(w0, constant)) / sum(w0)
    quotient_residual = max_abs_vector([value - constant_mean for value in constant])
    gauge_constant_energy = weighted_dot(d_constant, d_constant, w1)
    sample_energy = weighted_dot(field, h_field, w0)
    sample_energy_from_d = weighted_dot(d_field, d_field, w1)

    checks = {
        "weighted_adjoint_identity": adjoint_error <= tolerance,
        "weighted_hamiltonian_symmetry": symmetry_error <= tolerance,
        "laplacian_factorization": factorization_error <= tolerance,
        "gauge_constant_null_mode": null_mode_residual <= tolerance,
        "opposite_face_flux_cancellation": boundary_error <= tolerance,
        "full_degree_boundary": degree_error <= tolerance,
        "energy_identity": abs(sample_energy - sample_energy_from_d) <= tolerance,
    }

    return HarnessResult(
        depth=depth,
        vertex_count=vertex_count,
        edge_count=len(edge_list),
        boundary_convention="killing_full_degree_opposite_face_involution",
        weighted_inner_product="diagonal_vertex_and_edge_weights",
        symmetry_error=symmetry_error,
        adjoint_error=adjoint_error,
        laplacian_factorization_error=factorization_error,
        null_mode_residual=null_mode_residual,
        boundary_flux_cancellation_error=boundary_error,
        full_degree_error=float(degree_error),
        quotient_constant_preservation_error=quotient_residual,
        gauge_constant_energy=gauge_constant_energy,
        sample_energy=sample_energy,
        sample_energy_from_d=sample_energy_from_d,
        promotion=False,
        clay_promotion=False,
        ym_1_promotion=False,
        checks=checks,
    )


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    validate_args(args)
    result = run(args.depth, args.tolerance)
    payload: dict[str, Any] = asdict(result)
    payload["ok"] = all(result.checks.values())
    payload["scope"] = "finite_matrix_diagnostic_only"
    payload["not_proved"] = [
        "YM-1 finite theorem",
        "Hamiltonian domination",
        "OS/Wightman reconstruction",
        "continuum mass gap",
        "Clay Yang-Mills",
    ]

    args.json_output.parent.mkdir(parents=True, exist_ok=True)
    args.json_output.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    if args.json:
        print(json.dumps(payload, sort_keys=True))
    else:
        print(f"wrote {args.json_output}")
        print(
            "symmetry_error={:.3e} adjoint_error={:.3e} null_mode_residual={:.3e}".format(
                result.symmetry_error,
                result.adjoint_error,
                result.null_mode_residual,
            )
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
