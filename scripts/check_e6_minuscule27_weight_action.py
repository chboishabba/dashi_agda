#!/usr/bin/env python3
"""Exact finite audit for the E8 -> E6 x A2 mixed 27 and the E6 minuscule weight orbit.

Execution evidence only; not an Agda/Lean kernel proof.

The script:
* builds the standard doubled-coordinate 240 E8 roots;
* extracts the 72-root E6 subsystem and 6-root A2 subsystem;
* selects one of the six 27-root mixed fibres by its A2-weight component;
* orthogonally projects that fibre to the E6 subspace;
* checks the 27 projected weights have the expected two-distance geometry;
* checks root-difference adjacency is 16-regular;
* checks every E6 root reflection preserves the selected fibre and that
  projection intertwines all 72 reflections;
* verifies the induced Weyl action is transitive;
* greedily selects six independent E6 roots and verifies their permutations of
  the 27 weights generate a group of order 51840.
"""

from collections import Counter, defaultdict, deque
from fractions import Fraction as F
from itertools import product


def standard_e8_roots():
    roots = []
    for i in range(8):
        for j in range(i + 1, 8):
            for si, sj in product((-2, 2), repeat=2):
                x = [0] * 8
                x[i], x[j] = si, sj
                roots.append(tuple(F(v) for v in x))
    for signs in product((-1, 1), repeat=8):
        if sum(v < 0 for v in signs) % 2 == 0:
            roots.append(tuple(F(v) for v in signs))
    assert len(roots) == len(set(roots)) == 240
    return roots


def dot(x, y):
    return sum(a * b for a, b in zip(x, y))


def average_last_three(root):
    return sum(root[5:]) / 3


def a2_component(root):
    av = average_last_three(root)
    return tuple(v - av for v in root[5:])


def e6_projection(root):
    av = average_last_three(root)
    return tuple(root[:5]) + (av, av, av)


def reflect(v, root):
    coefficient = 2 * dot(v, root) / dot(root, root)
    return tuple(x - coefficient * a for x, a in zip(v, root))


def rank(vectors):
    rows = [list(v) for v in vectors]
    if not rows:
        return 0
    m, n = len(rows), len(rows[0])
    row = col = 0
    while row < m and col < n:
        pivot = next((r for r in range(row, m) if rows[r][col] != 0), None)
        if pivot is None:
            col += 1
            continue
        rows[row], rows[pivot] = rows[pivot], rows[row]
        p = rows[row][col]
        rows[row] = [x / p for x in rows[row]]
        for r in range(m):
            if r != row and rows[r][col] != 0:
                q = rows[r][col]
                rows[r] = [x - q * y for x, y in zip(rows[r], rows[row])]
        row += 1
        col += 1
    return row


def compose(p, q):
    return tuple(p[q[i]] for i in range(len(p)))


def main():
    roots = standard_e8_roots()
    e6 = [r for r in roots if r[5:] in ((F(-1),) * 3, (F(0),) * 3, (F(1),) * 3)]
    a2 = [r for r in roots if sorted(r[5:]) == [F(-2), F(0), F(2)]]
    mixed = [r for r in roots if r not in e6 and r not in a2]

    assert len(e6) == 72
    assert len(a2) == 6
    assert len(mixed) == 162

    fibres = defaultdict(list)
    for r in mixed:
        fibres[a2_component(r)].append(r)
    assert sorted(len(v) for v in fibres.values()) == [27] * 6

    fibre_key = sorted(fibres.keys())[0]
    fibre = fibres[fibre_key]
    fibre_set = set(fibre)
    weights = [e6_projection(r) for r in fibre]
    weight_set = set(weights)
    assert len(weight_set) == 27

    norms = Counter(dot(w, w) for w in weights)
    assert norms == Counter({F(16, 3): 27})

    inner_products = Counter(
        dot(weights[i], weights[j])
        for i in range(27) for j in range(i + 1, 27)
    )
    assert inner_products == Counter({F(4, 3): 216, F(-8, 3): 135})

    e6_set = set(e6)
    degrees = []
    for i, w in enumerate(weights):
        degree = 0
        for j, z in enumerate(weights):
            if i == j:
                continue
            difference = tuple(a - b for a, b in zip(w, z))
            if difference in e6_set:
                degree += 1
        degrees.append(degree)
    assert Counter(degrees) == Counter({16: 27})

    reflection_coefficients = Counter()
    for root in e6:
        for original in fibre:
            reflected = reflect(original, root)
            reflection_coefficients[2 * dot(original, root) / dot(root, root)] += 1
            assert reflected in fibre_set
            assert e6_projection(reflected) == reflect(e6_projection(original), root)
    assert set(reflection_coefficients) <= {F(-1), F(0), F(1)}

    start = next(iter(weight_set))
    seen = {start}
    queue = deque([start])
    while queue:
        w = queue.popleft()
        for root in e6:
            z = reflect(w, root)
            assert z in weight_set
            if z not in seen:
                seen.add(z)
                queue.append(z)
    assert len(seen) == 27

    simple_generators = []
    for root in e6:
        if rank(simple_generators + [root]) > len(simple_generators):
            simple_generators.append(root)
        if len(simple_generators) == 6:
            break
    assert len(simple_generators) == 6

    ordered_weights = sorted(weight_set)
    index = {w: i for i, w in enumerate(ordered_weights)}
    generators = [
        tuple(index[reflect(w, root)] for w in ordered_weights)
        for root in simple_generators
    ]
    identity = tuple(range(27))
    group = {identity}
    queue = deque([identity])
    while queue:
        g = queue.popleft()
        for s in generators:
            h = compose(s, g)
            if h not in group:
                group.add(h)
                queue.append(h)
    assert len(group) == 51840

    print("E8 roots                         = 240")
    print("E6 roots                         = 72")
    print("A2 roots                         = 6")
    print("mixed fibres                     = 6 x 27")
    print("selected projected weights       = 27")
    print("weight norm^2                    = 16/3")
    print("pair inner products              = 216*(4/3) + 135*(-8/3)")
    print("root-difference graph degree     = 16 on all 27 weights")
    print("all 72 E6 reflections preserve fibre and commute with projection")
    print("weight orbit                     = 27 (transitive)")
    print("generated permutation-group size = 51840")
    print("RUN_TERMINAL COMPLETE")


if __name__ == "__main__":
    main()
