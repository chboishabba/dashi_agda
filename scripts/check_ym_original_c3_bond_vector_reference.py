#!/usr/bin/env python3
"""Deterministic, independent reference for the original periodic YM bond C3.

Matches the old native side-four source:
  site C3 (x0,x1,x2,x3) -> (x0,x3,x1,x2)
  axis C3 0->0, 1->2, 2->3, 3->1
This checks the exact finite bond-vector reindexing, composition and orbit
counts for sides 1..5. It is NOT an Agda kernel check, Haar theorem,
physical continuum-limit theorem, or a claim about a 5D KK reduction.
"""
from itertools import product


def labels(side):
    # Original Torus.productFinite periodicTorus4Finite × axis4 order
    return [(*site, axis) for site in product(range(side), repeat=4)
            for axis in range(4)]


def c3(label):
    x0, x1, x2, x3, axis = label
    return (x0, x3, x1, x2, (0, 2, 3, 1)[axis])


def inverse_c3(label):
    x0, x1, x2, x3, axis = label
    return (x0, x2, x3, x1, (0, 3, 1, 2)[axis])


def reindex(values, indices, move):
    return [values[indices[move(label)]] for label in indices]


def verify(side):
    domain = labels(side)
    position = {label: i for i, label in enumerate(domain)}
    assert len(domain) == len(position) == 4 * side**4
    assert set(map(c3, domain)) == set(domain)
    assert set(map(inverse_c3, domain)) == set(domain)
    assert all(inverse_c3(c3(b)) == c3(inverse_c3(b)) == b for b in domain)

    v = list(range(len(domain)))  # distinguishing every physical coordinate
    forward = reindex(v, position, c3)
    backward = reindex(v, position, inverse_c3)
    assert reindex(forward, position, c3) != v or side == 1
    assert reindex(reindex(forward, position, c3), position, c3) == v
    assert reindex(backward, position, c3) == v
    assert reindex(forward, position, inverse_c3) == v

    # Old native Weld.nativeForwardC3Bonds is exactly field(C3 bond).
    assert all(forward[i] == v[position[c3(label)]]
               for i, label in enumerate(domain))
    wrong_axis = lambda label: (label[0], label[3], label[1], label[2], label[4])
    assert any(forward[i] != v[position[wrong_axis(label)]]
               for i, label in enumerate(domain))

    visited = set()
    cycles = []
    for start in domain:
        if start in visited:
            continue
        orbit = []
        current = start
        while current not in visited:
            visited.add(current)
            orbit.append(current)
            current = c3(current)
        assert current == start
        assert len(orbit) in (1, 3)
        cycles.append(orbit)
    fixed = sum(len(c) == 1 for c in cycles)
    three = sum(len(c) == 3 for c in cycles)
    assert fixed == side**2
    assert three == (4 * side**4 - side**2) // 3
    assert fixed + 3 * three == len(domain)
    print(f"L={side}: bonds={len(domain)}, fixed={fixed}, "
          f"3-cycles={three}; inverse, cube and wrong-axis controls passed")


if __name__ == "__main__":
    for side in (1, 2, 3, 4, 5):
        verify(side)
    print("reference status: PASS (finite source only; kernel pending)")
