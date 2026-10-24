#!/usr/bin/env python3
"""Finite linear-algebra experiment for IIT lattice/hyperfabric scaling.

This is numerical evidence only.  It does not inspect Agda source and does not
promote rank/cardinality observations into formal same-object theorems.

The 2D torus is also reported explicitly as a fabric of local 2-in/1-out
synthesis cells.  Each target (i,j) receives named A/B wires from (i+1,j) and
(i,j+1).  This makes the grid-wide recurrence geometry visible independently
of whether the local synthesis algebra is XOR, triXor, or another matched gate.
"""

from __future__ import annotations

from collections import defaultdict
from itertools import combinations, product
from math import log2


def index(coord: tuple[int, ...], n: int) -> int:
    value = 0
    scale = 1
    for c in coord:
        value += c * scale
        scale *= n
    return value


def linear_matrix(n: int, dim: int, q: int, axes: tuple[int, ...]):
    size = n**dim
    matrix = [[0 for _ in range(size)] for _ in range(size)]
    for coord in product(range(n), repeat=dim):
        row = index(coord, n)
        for axis in axes:
            source = list(coord)
            source[axis] = (source[axis] + 1) % n
            col = index(tuple(source), n)
            matrix[row][col] = (matrix[row][col] + 1) % q
    return matrix


def rank_mod(matrix, q: int) -> int:
    m = [row[:] for row in matrix]
    rows = len(m)
    cols = len(m[0]) if rows else 0
    rank = 0
    for col in range(cols):
        pivot = next((r for r in range(rank, rows) if m[r][col] % q), None)
        if pivot is None:
            continue
        m[rank], m[pivot] = m[pivot], m[rank]
        inverse = pow(m[rank][col] % q, -1, q)
        m[rank] = [(x * inverse) % q for x in m[rank]]
        for r in range(rows):
            if r != rank and m[r][col] % q:
                factor = m[r][col] % q
                m[r] = [(a - factor * b) % q for a, b in zip(m[r], m[rank])]
        rank += 1
        if rank == rows:
            break
    return rank


def slab_cut(n: int, dim: int, q: int, axes: tuple[int, ...]):
    side = lambda c: 0 if c[0] == 0 else 1
    crossing = 0
    affected = set()
    for coord in product(range(n), repeat=dim):
        target = index(coord, n)
        for axis in axes:
            source = list(coord)
            source[axis] = (source[axis] + 1) % n
            source = tuple(source)
            if side(coord) != side(source):
                crossing += 1
                affected.add(target)
    effect_bits = len(affected) * log2(q)
    return crossing, len(affected), effect_bits


def scaling_row(q: int, n: int, dim: int, axes: tuple[int, ...]):
    sites = n**dim
    rank = rank_mod(linear_matrix(n, dim, q, axes), q)
    kernel = sites - rank
    crossing, affected, effect_bits = slab_cut(n, dim, q, axes)
    selectivity = q ** (-kernel)
    return {
        "q": q,
        "n": n,
        "dimension": dim,
        "sites": sites,
        "rank": rank,
        "kernel_dimension": kernel,
        "global_configurations": q**sites,
        "reachable_states": q**rank,
        "predecessors_per_reachable_state": q**kernel,
        "slab_crossing_edges": crossing,
        "slab_affected_targets": affected,
        "slab_effect_bits": effect_bits,
        "cause_selectivity": selectivity,
        "declared_slab_min_bits": selectivity * effect_bits,
    }


def two_input_fabric_metrics(n: int) -> dict:
    """Directed toroidal gluing graph for the east+south 2->1 synthesis rule."""
    nodes = tuple(product(range(n), repeat=2))
    edges = []
    for target in nodes:
        i, j = target
        source_a = ((i + 1) % n, j)
        source_b = (i, (j + 1) % n)
        edges.append((source_a, target, "A"))
        edges.append((source_b, target, "B"))

    adjacency = defaultdict(list)
    reverse = defaultdict(list)
    for source, target, _port in edges:
        adjacency[source].append(target)
        reverse[target].append(source)

    seen = set()
    order = []

    def visit(node):
        seen.add(node)
        for nxt in adjacency[node]:
            if nxt not in seen:
                visit(nxt)
        order.append(node)

    for node in nodes:
        if node not in seen:
            visit(node)

    seen.clear()
    components = []

    def reverse_visit(node, component):
        seen.add(node)
        component.append(node)
        for nxt in reverse[node]:
            if nxt not in seen:
                reverse_visit(nxt, component)

    for node in reversed(order):
        if node not in seen:
            component = []
            reverse_visit(node, component)
            components.append(component)

    indegrees = {node: len(reverse[node]) for node in nodes}
    outdegrees = {node: len(adjacency[node]) for node in nodes}
    return {
        "n": n,
        "local_synthesis_cells": len(nodes),
        "directed_named_wires": len(edges),
        "all_indegrees": sorted(set(indegrees.values())),
        "all_outdegrees": sorted(set(outdegrees.values())),
        "strongly_connected_components": len(components),
        "largest_scc_sites": max(map(len, components)),
        "explicit_axial_cycles": 2 * n,
        "axial_cycle_length": n,
        "interpretation": "global recurrence is gluing of local 2-input/1-output cells",
    }


def cube_two_face_projection_ranks():
    q = 3
    n = 3
    axes = (0, 1, 2)
    matrix = linear_matrix(n, 3, q, axes)
    image_dimension = rank_mod(matrix, q)
    coords = list(product(range(3), repeat=3))
    rows = []
    for axis in range(3):
        for pair in combinations(range(3), 2):
            selected = [index(c, n) for c in coords if c[axis] in pair]
            restricted = [matrix[i] for i in selected]
            projection_rank = rank_mod(restricted, q)
            rows.append({
                "axis": axis,
                "faces": pair,
                "projection_rank": projection_rank,
                "image_dimension": image_dimension,
                "bijective_on_image": projection_rank == image_dimension,
            })
    return rows


def main() -> None:
    rows = []
    for q in (2, 3):
        for n in range(2, 11):
            rows.append(scaling_row(q, n, 2, (0, 1)))
        rows.append(scaling_row(q, 3, 3, (0, 1, 2)))

    print("# lattice scaling")
    for row in rows:
        print(row)

    print("# grid as repeated 2-input/1-output synthesis fabric")
    for n in (2, 3, 10):
        print(two_input_fabric_metrics(n))

    print("# 3x3x3 ternary two-face projection")
    for row in cube_two_face_projection_ranks():
        print(row)

    print("# cardinality landmarks")
    print({"27^3": 27**3, "3^9": 3**9, "9^9": 9**9, "3^18": 3**18, "3^27": 3**27})


if __name__ == "__main__":
    main()
