#!/usr/bin/env python3
from __future__ import annotations

import json
from collections import deque

import sympy as sp
from sympy.matrices.normalforms import smith_normal_form


def compute_receipt() -> dict[str, object]:
    # E8 Cartan matrix in a simple-root basis: A7 chain with a branch at node 2.
    edges = ((0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (2, 7))
    cartan = sp.eye(8) * 2
    for i, j in edges:
        cartan[i, j] = -1
        cartan[j, i] = -1

    ident = sp.eye(8)
    reflections = []
    for i in range(8):
        e = sp.zeros(8, 1)
        e[i] = 1
        reflections.append(ident - e * cartan.row(i))

    coxeter = ident
    for s in reflections:
        coxeter = s * coxeter

    # E8 Coxeter number is 30; c^10 has order three and no fixed vector.
    w = coxeter**10
    assert w**3 == ident
    assert (w - ident).rank() == 8

    one_minus_w = ident - w
    smith = smith_normal_form(one_minus_w, domain=sp.ZZ)
    smith_diagonal = tuple(abs(int(smith[i, i])) for i in range(8))
    assert smith_diagonal == (1, 1, 1, 1, 3, 3, 3, 3)

    def tupcol(v: sp.Matrix) -> tuple[int, ...]:
        return tuple(int(v[i]) for i in range(v.rows))

    root0 = sp.zeros(8, 1)
    root0[0] = 1
    roots = {tupcol(root0)}
    queue = deque([root0])
    while queue:
        root = queue.popleft()
        for s in reflections:
            nxt = s * root
            key = tupcol(nxt)
            if key not in roots:
                roots.add(key)
                queue.append(nxt)

    assert len(roots) == 240
    assert all(int((sp.Matrix(r).T * cartan * sp.Matrix(r))[0]) == 2 for r in roots)

    def wact(r: tuple[int, ...]) -> tuple[int, ...]:
        return tupcol(w * sp.Matrix(r))

    seen: set[tuple[int, ...]] = set()
    orbits: list[tuple[tuple[int, ...], ...]] = []
    for root in roots:
        if root in seen:
            continue
        orbit = []
        x = root
        for _ in range(3):
            orbit.append(x)
            seen.add(x)
            x = wact(x)
        assert x == root
        assert len(set(orbit)) == 3
        orbits.append(tuple(orbit))

    assert len(orbits) == 80

    # Since det(1-w)=81, membership in (1-w)E8 can be checked over Q by
    # solving (1-w)z=v and requiring z integral.
    inverse = one_minus_w.inv()

    def in_image(v: tuple[int, ...]) -> bool:
        z = inverse * sp.Matrix(v)
        return all(x.q == 1 for x in z)

    assert not any(in_image(root) for root in roots)

    representatives = [orbit[0] for orbit in orbits]
    for i, a in enumerate(representatives):
        for b in representatives[i + 1 :]:
            diff = tuple(a[j] - b[j] for j in range(8))
            assert not in_image(diff)

    return {
        "cartan_determinant": int(cartan.det()),
        "root_count": len(roots),
        "fixed_roots": 0,
        "order_three_orbits": len(orbits),
        "orbit_size": 3,
        "det_one_minus_w": int(one_minus_w.det()),
        "smith_diagonal": smith_diagonal,
        "quotient_order": abs(int(one_minus_w.det())),
        "nonzero_quotient_classes_hit_by_roots": len(orbits),
        "roots_per_nonzero_class": 3,
        "all_root_orbits_distinct_mod_image": True,
    }


if __name__ == "__main__":
    print(json.dumps(compute_receipt(), indent=2, sort_keys=True))
