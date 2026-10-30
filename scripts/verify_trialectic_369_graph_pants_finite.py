#!/usr/bin/env python3
"""Deterministic finite semantics audit for the Agda golden 369 graph/pants lane.

This is an executed-combinatorics *companion*, not a proof checker.
Agda/Lean kernel status MUST be established separately.  No external
dependencies, randomized sampling, Monster representation or smooth-surface
claims.  Source model: native -1<->0<->+1 one-step ternary geometry;
not an arbitrary-coordinate-difference/hyperedge replacement.

Source prompt: Tivadar Danka, 26 Oct 2026 matrix-as-graph illustration.
The matrix/graph correspondence is standard mathematical prior art.
DASHI authors this finite integration/audit program.
"""

from __future__ import annotations

from collections import Counter
from itertools import permutations, product
import json


TRITS = (-1, 0, 1)
V = tuple(product(TRITS, repeat=3))
MATRIX_TENTHS = ((5, 10, 0), (2, 0, 22), (18, 20, 0))


def adjacent(x: tuple[int, ...], y: tuple[int, ...]) -> bool:
    diffs = tuple(abs(a - b) for a, b in zip(x, y, strict=True))
    return diffs.count(1) == 1 and diffs.count(0) == 2


def checker(x: tuple[int, ...]) -> int:
    return sum(t == 0 for t in x) % 2


def rotate(x: tuple[int, int, int]) -> tuple[int, int, int]:
    return (x[1], x[2], x[0])


def flip_second(x: tuple[int, int, int]) -> tuple[int, int, int]:
    return (x[0], -x[1], x[2])


def main() -> None:
    edges = tuple((x, y) for x in V for y in V if adjacent(x, y))
    assert len(V) == 27
    assert len(edges) == 108
    assert all(x != y for x, y in edges)
    assert len(edges) // 2 == 54
    assert all(checker(x) != checker(y) for x, y in edges)
    assert len({checker(x) for x in V}) == 2
    assert all(adjacent(rotate(x), rotate(y)) for x, y in edges)
    assert all(adjacent(flip_second(x), flip_second(y)) for x, y in edges)
    assert all(rotate(rotate(rotate(x))) == x for x in V)
    assert all(flip_second(flip_second(x)) == x for x in V)

    # All six distinct coordinate permutations, not only the C3 subgroup.
    anchor = (-1, 0, 1)
    six = tuple(permutations((0, 1, 2)))
    assert len(six) == 6
    assert len({tuple(anchor[i] for i in p) for p in six}) == 6
    for perm in six:
        assert all(
            adjacent(tuple(x[i] for i in perm), tuple(y[i] for i in perm))
            for x, y in edges
        )

    assert sum(weight != 0 for row in MATRIX_TENTHS for weight in row) == 6
    assert MATRIX_TENTHS[0][0] == 5
    assert MATRIX_TENTHS[1][1] == 0
    assert MATRIX_TENTHS[0][1] != MATRIX_TENTHS[1][0]
    assert MATRIX_TENTHS[0][2] == 0
    a2_ac = sum(MATRIX_TENTHS[0][k] * MATRIX_TENTHS[k][2]
                for k in range(3))
    assert a2_ac == 220

    receipt = {
        "authority": "finite exhaustive Python semantics only; Agda and Lean kernel pending",
        "grid_vertices": len(V),
        "directed_grid_edges": len(edges),
        "undirected_grid_edges": len(edges) // 2,
        "degree_histogram": dict(sorted(Counter(
            sum(adjacent(x, y) for y in V) for x in V
        ).items())),
        "minimal_palette_size": 2,
        "distinct_s3_permutations": len(six),
        "s3_preserves_nearest_neighbour_adjacency": True,
        "flip_and_rotation_preserve_adjacency": True,
        "fixture_arcs_including_loop": 6,
        "fixture_weighted_c3_invariant": False,
        "fixture_a_to_c_direct_tenths": 0,
        "fixture_a_to_c_two_step_hundredths": a2_ac,
        "pants_smoothness_claim": False,
        "triadic_face_decoded_from_graph_claim": False,
    }
    print(json.dumps(receipt, sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
