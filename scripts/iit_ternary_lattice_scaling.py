#!/usr/bin/env python3
"""Numerical scaling experiment for binary/ternary XOR-like lattices.

This is numeric/combinatorial only.  It does not inspect Agda source.

The 2D seed rule is the repo's 2x2 XOR fixture generalized to an n x n torus:

    x'_(i,j) = x_(i+1,j) + x_(i,j+1) mod q.

For the 3D 3x3x3 lattice we compare two rules:

* x+y control: independent stacked faces;
* x+y+z: genuine third-axis coupling, equivalently associative iteration of
  the same additive synthesis law.

For each finite linear system we compute rank over F_q, kernel dimension,
reachable-state count, and a geometric slab-cut effect penalty.  The cut
penalty is not claimed to be a full IIT MIP; it is the exact effect-side
penalty for this declared cut under independent uniform noising of crossing
inputs.
"""

from __future__ import annotations

import json
from itertools import product
from math import log2
from pathlib import Path


def state_index(coord: tuple[int, ...], n: int) -> int:
    value = 0
    stride = 1
    for c in coord:
        value += c * stride
        stride *= n
    return value


def torus_linear_matrix(
    n: int, dim: int, q: int, active_axes: tuple[int, ...]
) -> list[list[int]]:
    size = n**dim
    matrix = [[0] * size for _ in range(size)]
    for coord in product(range(n), repeat=dim):
        target = state_index(coord, n)
        for axis in active_axes:
            source = list(coord)
            source[axis] = (source[axis] + 1) % n
            source_index = state_index(tuple(source), n)
            matrix[target][source_index] = (
                matrix[target][source_index] + 1
            ) % q
    return matrix


def rank_mod(matrix: list[list[int]], q: int) -> int:
    work = [row[:] for row in matrix]
    rank = 0
    for column in range(len(work[0])):
        pivot = next(
            (row for row in range(rank, len(work)) if work[row][column] % q),
            None,
        )
        if pivot is None:
            continue
        work[rank], work[pivot] = work[pivot], work[rank]
        inverse = pow(work[rank][column] % q, -1, q)
        work[rank] = [(x * inverse) % q for x in work[rank]]
        for row in range(len(work)):
            if row != rank and work[row][column] % q:
                factor = work[row][column] % q
                work[row] = [
                    (a - factor * b) % q
                    for a, b in zip(work[row], work[rank])
                ]
        rank += 1
        if rank == len(work):
            break
    return rank


def geometric_slab_cut(
    n: int, dim: int, q: int, active_axes: tuple[int, ...], cut_axis: int = 0
) -> dict:
    """Cut coordinate-0 slab from the remaining torus sites."""

    def side(coord: tuple[int, ...]) -> int:
        return 0 if coord[cut_axis] == 0 else 1

    crossing_edges = 0
    affected_targets: set[int] = set()
    for coord in product(range(n), repeat=dim):
        target = state_index(coord, n)
        for axis in active_axes:
            source = list(coord)
            source[axis] = (source[axis] + 1) % n
            source_tuple = tuple(source)
            if side(coord) != side(source_tuple):
                crossing_edges += 1
                affected_targets.add(target)

    affected = len(affected_targets)
    return {
        "crossing_edges": crossing_edges,
        "affected_targets": affected,
        "effect_cut_penalty_bits": affected * log2(q),
    }


def experiment_row(
    q: int,
    n: int,
    dim: int,
    active_axes: tuple[int, ...],
    label: str,
) -> dict:
    sites = n**dim
    matrix = torus_linear_matrix(n, dim, q, active_axes)
    rank = rank_mod(matrix, q)
    return {
        "q": q,
        "label": label,
        "side_length": n,
        "dimension": dim,
        "causal_sites": sites,
        "global_configurations": q**sites,
        "linear_rank": rank,
        "kernel_dimension": sites - rank,
        "reachable_states": q**rank,
        "slab_cut": geometric_slab_cut(n, dim, q, active_axes),
    }


def lattice_scaling_summary() -> dict:
    experiments = []
    for q in (2, 3):
        for n in (2, 3, 4):
            experiments.append(
                experiment_row(q, n, 2, (0, 1), "2D east+south face")
            )
        experiments.append(
            experiment_row(q, 3, 3, (0, 1), "3D x+y stacked-face control")
        )
        experiments.append(
            experiment_row(q, 3, 3, (0, 1, 2), "3D x+y+z coupled cube")
        )

    return {
        "contract": "iit_ternary_lattice_scaling",
        "numeric_only": True,
        "cardinality": {
            "one_27_state_geometric_cube": 27,
            "three_27_state_factors": 27**3,
            "nine_ternary_sites": 3**9,
            "twenty_seven_ternary_sites": 3**27,
            "nine_tetration_level_2": 9**9,
        },
        "experiments": experiments,
        "interpretation_boundary": {
            "27_cubed_is_27_ternary_sites": False,
            "three_27_state_factors_equal_nine_ternary_site_cardinality": True,
            "ordinary_site_configuration_growth_is_tetration": False,
            "slab_cut_penalty_is_full_iit_mip": False,
        },
    }


def main() -> None:
    summary = lattice_scaling_summary()
    output = Path(__file__).with_name("data") / "outputs" / "iit_ternary_lattice_scaling.json"
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
    print(json.dumps(summary, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
