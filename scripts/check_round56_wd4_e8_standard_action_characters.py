#!/usr/bin/env python3
"""Exact W(D4) standard-coordinate action test on two 240-point carriers.

This is an alternative SAME-ACTOR action to the prior paired-fifth-axis
B4->W(D8) comparison. The common generators for W(D4) are the three
adjacent coordinate swaps and the three adjacent paired sign flips, all
on coordinates 0..3. E8 roots are doubled to integral coordinates.
This does NOT test every D4 embedding, Spin(8) representation, F4 folding,
E6 action, triality automorphism or F3-linear root-module intertwiner.
"""
from collections import deque
from itertools import combinations, product


def e8_roots_twice():
    root_set = set()
    for i, j in combinations(range(8), 2):
        for a, b in product((-2, 2), repeat=2):
            v = [0] * 8
            v[i], v[j] = a, b
            root_set.add(tuple(v))
    for v in product((-1, 1), repeat=8):
        if sum(x < 0 for x in v) % 2 == 0:
            root_set.add(v)
    assert len(root_set) == 240
    return root_set


def regular_grid_cells():
    cells = {
        v for v in product((-2, -1, 1, 2), repeat=4)
        if any(abs(x) == 2 for x in v)
    }
    assert len(cells) == 240
    return cells


def adjacent_swap(v, i):
    w = list(v)
    w[i], w[i + 1] = w[i + 1], w[i]
    return tuple(w)


def even_pair_flip(v, i):
    w = list(v)
    w[i], w[i + 1] = -w[i], -w[i + 1]
    return tuple(w)


def generators():
    return [*(lambda v, i=i: even_pair_flip(v, i) for i in range(3)),
            *(lambda v, i=i: adjacent_swap(v, i) for i in range(3))]


def orbits(points, gs):
    remaining = set(points)
    result = []
    while remaining:
        seed = min(remaining)
        seen = {seed}
        todo = deque([seed])
        while todo:
            v = todo.popleft()
            for g in gs:
                next_v = g(v)
                assert next_v in points
                if next_v not in seen:
                    seen.add(next_v)
                    todo.append(next_v)
        result.append(len(seen))
        remaining -= seen
    return sorted(result)


def test_standard_wd4_action_no_go():
    cells, roots, gs = regular_grid_cells(), e8_roots_twice(), generators()
    for carrier in (cells, roots):
        for g in gs:
            assert {g(v) for v in carrier} == carrier

    cf = [sum(g(x) == x for x in cells) for g in gs]
    rf = [sum(g(x) == x for x in roots) for g in gs]
    assert cf == [0, 0, 0, 56, 56, 56], cf
    assert rf == [60, 60, 60, 126, 126, 126], rf
    cell_orbits, root_orbits = orbits(cells, gs), orbits(roots, gs)
    assert cell_orbits == [8, 8, 32, 32, 32, 32, 48, 48], cell_orbits
    assert root_orbits.count(1) == 24, root_orbits
    assert sum(cell_orbits) == sum(root_orbits) == 240
    assert len(root_orbits) == 49, len(root_orbits)
    # A bijective group-set intertwiner preserves each generator's fixed
    # count AND its orbit partition. Neither necessary condition holds.
    assert cf != rf and cell_orbits != root_orbits
    # A conjugating isomorphism between the 240-dimensional permutation
    # representations over Q/C would preserve generator matrix traces.
    # Characteristic 3 caveat: traces 0 and 60 agree MODULO 3, likewise
    # 56 and 126 differ mod 3 (=2 versus 0), so the swap still witnesses
    # inequivalence over F3, at least for invertible linear equivalence.
    assert (cf[3] - rf[3]) % 3 != 0
    print("PASS: two 240-point closed W(D4)-action carriers")
    print("fixed counts (grid/E8):", cf, rf)
    print("orbit partitions (grid/E8):", cell_orbits, root_orbits)
    print("NO equivariant set bijection; NO invertible linear F3/Q/C intertwiner")
    print("SCOPE: this selected standard-coordinate W(D4) action only")


if __name__ == "__main__":
    test_standard_wd4_action_no_go()
