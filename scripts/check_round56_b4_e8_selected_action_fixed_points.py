#!/usr/bin/env python3
"""Exact finite no-go for ONE chosen B4 embedding in W(E8).

Original DASHI finite analysis; standard E8 roots are mathematical prior art.
Source regular cells: DASHI.Physics.YangMills.BalabanClayT4HypercubicOrbitGeometryExact.
Not a no-go for other B4 embeddings, F4/E6/D4 quotients, or linear intertwiners.
No floating point, external libraries, geometry inference, or empirical claims.
"""
from collections import Counter, deque
from itertools import combinations, product


def e8_roots_twice():
    """Root coordinates scaled by 2 to retain exact integers."""
    result = set()
    for i, j in combinations(range(8), 2):
        for a, b in product((-2, 2), repeat=2):
            v = [0] * 8
            v[i], v[j] = a, b
            result.add(tuple(v))
    for v in product((-1, 1), repeat=8):
        if sum(x < 0 for x in v) % 2 == 0:
            result.add(v)
    assert len(result) == 240
    return result


def regular_cells():
    """Two inner and two outer signed cells per coordinate; omit 2^4 core."""
    return {
        v for v in product((-2, -1, 1, 2), repeat=4)
        if any(abs(x) == 2 for x in v)
    }


def swap(v, i):
    result = list(v)
    result[i], result[i + 1] = result[i + 1], result[i]
    return tuple(result)


def grid_flip(v, i):
    result = list(v)
    result[i] = -result[i]
    return tuple(result)


def root_paired_flip(v, i):
    """Even-sign Weyl(D8) action; i=0..3, pair with coordinate 4."""
    result = list(v)
    result[i] = -result[i]
    result[4] = -result[4]
    return tuple(result)


def orbits(carrier, generators):
    remaining = set(carrier)
    sizes = []
    while remaining:
        seed = min(remaining)
        orbit, queue = {seed}, deque([seed])
        while queue:
            v = queue.popleft()
            for g in generators:
                nxt = g(v)
                assert nxt in carrier, "Action is not closed on carrier"
                if nxt not in orbit:
                    orbit.add(nxt)
                    queue.append(nxt)
        remaining.difference_update(orbit)
        sizes.append(len(orbit))
    return sorted(sizes)


def run():
    grid, roots = regular_cells(), e8_roots_twice()
    assert len(grid) == len(roots) == 240

    grid_gens = [
        *(lambda v, i=i: grid_flip(v, i) for i in range(4)),
        *(lambda v, i=i: swap(v, i) for i in range(3)),
    ]
    root_gens = [
        *(lambda v, i=i: root_paired_flip(v, i) for i in range(4)),
        *(lambda v, i=i: swap(v, i) for i in range(3)),
    ]
    for carrier, gens in ((grid, grid_gens), (roots, root_gens)):
        for gen in gens:
            assert {gen(v) for v in carrier} == carrier

    grid_fixed = [sum(g(v) == v for v in grid) for g in grid_gens]
    root_fixed = [sum(g(v) == v for v in roots) for g in root_gens]
    assert grid_fixed == [0, 0, 0, 0, 56, 56, 56], grid_fixed
    assert root_fixed == [60, 60, 60, 60, 126, 126, 126], root_fixed

    grid_orbits, root_orbits = orbits(grid, grid_gens), orbits(roots, root_gens)
    assert grid_orbits == [16, 64, 64, 96], grid_orbits
    assert sum(root_orbits) == 240
    assert Counter(root_orbits)[1] == 12, root_orbits

    # An equivariant bijection preserves each generator's fixed-point set.
    # Disagreement gives an exact specific-action no-go.
    assert any(a != b for a, b in zip(grid_fixed, root_fixed))
    print("PASS: two closed 240-element carriers; seven matched generators")
    print("grid generator fixed counts:", grid_fixed)
    print("E8 generator fixed counts:", root_fixed)
    print("grid orbit sizes:", grid_orbits)
    print("E8 orbit sizes:", root_orbits)
    print("RESULT: NO equivariant bijection for this paired-flip B4 embedding")
    print("BOUNDARY: alternative root actions and linear intertwiners NOT ruled out")


if __name__ == "__main__":
    run()
