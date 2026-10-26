#!/usr/bin/env python3
"""Exact finite Burnside quotient of the MIXED8 ten-sheet source chart.

SOURCE/ATTRIBUTION:
- Reuses the original #1098 AtlasRep-sourced D4 quotient type E+E and
  #1250's MIXED8 (=axis4 disjoint union diagonal4) balanced fibre model.
- Orbit-stabilizer/Burnside and D4 representation theory are classical.
- This is a new DASHI finite-model computation; NOT an AtlasRep,
  Barraclough--Wilson, BMW, Monster or IIT source-intertwiner receipt.
- Does not identify the chosen affine chart under the entire Heisenberg group.
No GAP, mmgroup or Agda kernel claim is made.
"""
from itertools import product
from collections import Counter

F = range(3)
E = tuple(product(F, repeat=2))
V = tuple(product(F, repeat=4))
X = tuple(x for x in V if x != (0, 0, 0, 0))
Y = tuple(y for y in E if y != (0, 0))


def rotate(v):
    """Standard E generator (x,y)->(-y,x) on each E direct summand."""
    return tuple(z for x, y in zip(v[::2], v[1::2])
                 for z in ((-y) % 3, x))


def reflect(v):
    """Standard E mirror (x,y)->(x,-y) on each E direct summand."""
    return tuple(z for x, y in zip(v[::2], v[1::2])
                 for z in (x, (-y) % 3))


def orbit(v):
    todo = [v]
    seen = {v}
    while todo:
        x = todo.pop()
        for z in (rotate(x), reflect(x)):
            if z not in seen:
                seen.add(z)
                todo.append(z)
    return frozenset(seen)


def kind(y):
    return "axis" if ((y[0] == 0) != (y[1] == 0)) else "diagonal"


def source_orbits():
    remain = set(X)
    result = []
    while remain:
        rep = min(remain)
        o = orbit(rep)
        assert o <= remain
        result.append((rep, o))
        remain -= o
    return tuple(result)


def local_map(x, y):
    """D4-map on one orbit sending x to y, or None for a bad stabilizer."""
    mapping = {x: y}
    todo = [x]
    while todo:
        v = todo.pop()
        for on_v, on_y in ((rotate, rotate), (reflect, reflect)):
            w, z = on_v(v), on_y(mapping[v])
            if w in mapping:
                if mapping[w] != z:
                    return None
            else:
                mapping[w] = z
                todo.append(w)
    return mapping


def source_linear_automorphisms():
    """Centralizer in GL4(F3) is GL2(F3), acting on the two E copies.

    Indeed commuting with reflect on E forces a diagonal 2x2 matrix;
    commuting with rotate makes it scalar. So End_D4(E)=F3, and the
    centralizer on E+E is M2(F3), with units GL2(F3).
    """
    for a, b, c, d in product(F, repeat=4):
        if (a*d - b*c) % 3 == 0:
            continue

        def act(v, a=a, b=b, c=c, d=d):
            x, y, u, w = v
            return ((a*x+b*u) % 3, (a*y+b*w) % 3,
                    (c*x+d*u) % 3, (c*y+d*w) % 3)

        assert all(rotate(act(v)) == act(rotate(v)) and
                   reflect(act(v)) == act(reflect(v)) for v in X)
        yield (a, b, c, d), act


def target_automorphism(y, signs):
    """Aut_D4(Y)=C2 x C2: independent antipodes on the two 4-orbits."""
    s = signs[0 if kind(y) == "axis" else 1]
    return tuple(s*a % 3 for a in y)


def fixed_balanced_count(source_perm, target_signs, orbs, opts, membership):
    """Fixed maps under f(Ax)=T f(x), counted by orbit-cycle DP.

    Every free source 8-orbit assigned to axis contributes exactly two
    preimages per axis target point. Four axis 4-orbits already contribute
    one each; balancing requires exactly THREE of six free orbits to axis.
    """
    source_inverse = {source_perm[x]: x for x in X}
    next_orbit, transitions = [], []
    for i, (rep, o) in enumerate(orbs):
        j = membership[source_perm[rep]]
        next_orbit.append(j)
        rep_j = orbs[j][0]
        x_back = source_inverse[rep_j]
        transitions.append([
            next(k for k, (yy, _) in enumerate(opts[j])
                 if yy == target_automorphism(mapping[x_back], target_signs))
            for y, mapping in opts[i]
        ])
    assert sorted(next_orbit) == list(range(len(orbs)))
    remaining = set(range(len(orbs)))
    poly = [1, 0, 0, 0]
    while remaining:
        i = min(remaining)
        cycle = [i]
        j = next_orbit[i]
        while j != i:
            assert j not in cycle
            cycle.append(j)
            j = next_orbit[j]
        remaining.difference_update(cycle)
        choices = Counter()
        for k in range(len(opts[i])):
            mapped = k
            j = i
            for _ in cycle:
                mapped = transitions[j][mapped]
                j = next_orbit[j]
            if mapped != k:
                continue
            exponent = (len(cycle) if len(orbs[i][1]) == 8 and
                        kind(opts[i][k][0]) == "axis" else 0)
            choices[exponent] += 1
        out = [0, 0, 0, 0]
        for count, n in enumerate(poly):
            for increment, ways in choices.items():
                if count + increment <= 3:
                    out[count + increment] += n * ways
        poly = out
    return poly[3]


def compute():
    orbs = source_orbits()
    assert Counter(len(o) for _, o in orbs) == {4: 8, 8: 6}
    membership = {x: i for i, (_, o) in enumerate(orbs) for x in o}
    opts = []
    for rep, o in orbs:
        choices = []
        for y in Y:
            mapping = local_map(rep, y)
            if mapping is not None:
                assert set(mapping) == set(o)
                choices.append((y, mapping))
        opts.append(choices)
    assert sorted(map(len, opts)) == [2]*8 + [8]*6
    assert sum(len(o) == 4 and kind(opts[i][0][0]) == "axis"
               for i, (_, o) in enumerate(orbs)) == 4

    gl2 = list(source_linear_automorphisms())
    assert len(gl2) == 48
    fixed_histogram = Counter()
    for mat, act in gl2:
        p = {x: act(x) for x in X}
        for signs in product((1, 2), repeat=2):
            fixed_histogram[fixed_balanced_count(
                p, signs, orbs, opts, membership)] += 1

    # Original #1250 count, independently also given by C(6,3)*2^8*4^6.
    total = 20_971_520
    assert total == 20 * 2**8 * 4**6
    assert fixed_histogram[total] == 2
    assert sum(fixed_histogram.values()) == 48*4
    fixed_sum = sum(n*mult for n, mult in fixed_histogram.items())
    assert fixed_sum % (48*4) == 0
    result = fixed_sum // (48*4)
    assert result == 218_496
    return {
        "schema": "monster3b-mixed8-source-linear-burnside-v1",
        "source_D4_orbit_sizes": {"4": 8, "8": 6},
        "source_linear_automorphism_order": 48,
        "target_equivariant_automorphism_order": 4,
        "balanced_maps": total,
        "fixed_count_histogram": dict(sorted(fixed_histogram.items())),
        "fixed_point_sum": fixed_sum,
        "orbits_source_linear_and_target_equivariant": result,
        "authentic_monster_word_or_full_Heisenberg_intertwiner": False,
        "actual_suzuki_78_family_source_selected": False,
        "agda_kernel_checked": False,
        "status": "EXACT_FINITE_CHART_ONLY"
    }


if __name__ == "__main__":
    import json
    print(json.dumps(compute(), indent=2, sort_keys=True))
