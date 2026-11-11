#!/usr/bin/env python3
"""Finite Round56 rank-two versus two independently labelled F4 root systems.

Tests the *standard* W(B4) signed coordinate action and its W(D4)
even-sign subgroup on the original rank-two 96 grid cells and TWO copies
of the usual F4 48-root set (all coordinates doubled to integers).

Does NOT test the alternative E6-folded action from PR #1106,
the Albert/first-Tits representation, a triality-twisted action, or an
unlabelled tensor/linear representation with different group generators.
"""
from collections import deque
from itertools import combinations, product


def rank_two_grid():
    s = {
        tuple(p) for p in product((-2, -1, 1, 2), repeat=4)
        if sum(abs(x) == 2 for x in p) == 2
    }
    assert len(s) == 96
    return s


def f4_roots_doubled():
    roots = set()
    for i in range(4):
        for a in (-2, 2):
            r = [0] * 4
            r[i] = a
            roots.add(tuple(r))
    for i, j in combinations(range(4), 2):
        for a, b in product((-1, 1), repeat=2):
            r = [0] * 4
            r[i], r[j] = a, b
            roots.add(tuple(r))
    roots.update(product((-1, 1), repeat=4))
    assert len(roots) == 48
    return roots


def flip(v, i):
    r = list(v)
    r[i] = -r[i]
    return tuple(r)


def swap(v, i):
    r = list(v)
    r[i], r[i + 1] = r[i + 1], r[i]
    return tuple(r)


def pair_flip(v, i):
    return flip(flip(v, i), i + 1)


def generators(even=False):
    fs = ([lambda v, i=i: pair_flip(v, i) for i in range(3)]
          if even else [lambda v, i=i: flip(v, i) for i in range(4)])
    return fs + [lambda v, i=i: swap(v, i) for i in range(3)]


def orbits(carrier, generators):
    remaining = set(carrier)
    sizes = []
    while remaining:
        seed = min(remaining)
        q, visited = deque([seed]), {seed}
        while q:
            v = q.popleft()
            for g in generators:
                w = g(v)
                assert w in carrier
                if w not in visited:
                    visited.add(w)
                    q.append(w)
        remaining -= visited
        sizes.append(len(visited))
    return sorted(sizes)


def check():
    grid, roots = rank_two_grid(), f4_roots_doubled()
    copies = {(label, r) for label in (0, 1) for r in roots}
    assert len(copies) == len(grid) == 96

    for even in (False, True):
        name = "W(D4)" if even else "W(B4)"
        gs = generators(even)
        lifted = [lambda item, g=g: (item[0], g(item[1])) for g in gs]
        grid_orbits = orbits(grid, gs)
        root_orbits = orbits(roots, gs)
        copy_orbits = orbits(copies, lifted)
        grid_fixed = [sum(g(v) == v for v in grid) for g in gs]
        target_fixed = [sum(g(v) == v for v in copies) for g in lifted]

        if not even:
            assert grid_orbits == [96]
            assert root_orbits == [8, 16, 24]
            assert copy_orbits == [8, 8, 16, 16, 24, 24]
            assert grid_fixed == [0, 0, 0, 0, 16, 16, 16]
            assert target_fixed == [36] * 7
            swap_index = 4
        else:
            assert grid_orbits == [48, 48]
            assert root_orbits == [8, 8, 8, 24]
            assert copy_orbits == [8, 8, 8, 8, 8, 8, 24, 24]
            assert grid_fixed == [0, 0, 0, 16, 16, 16]
            assert target_fixed == [16, 16, 16, 36, 36, 36]
            swap_index = 3

        assert (grid_fixed[swap_index] - target_fixed[swap_index]) % 3 != 0
        print(name, "grid orbits", grid_orbits, "F4 copies", copy_orbits)
        print(name, "fixed-point counts", grid_fixed, target_fixed)
        print(name, "swap traces mod 3",
              grid_fixed[swap_index] % 3, target_fixed[swap_index] % 3)
        print(name, "PASS selected-action bijection / invertible F3 intertwiner no-go")

    print("BOUNDARY: folded E6/F4 and nonstandard triality actions remain untested")


if __name__ == "__main__":
    check()
