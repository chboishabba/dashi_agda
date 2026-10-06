#!/usr/bin/env python3
from __future__ import annotations

import json
from collections import Counter, deque

import sympy as sp

P = 3

# Exact standard-coordinate quotient map U : Z^8 -> F3^4.
U = sp.Matrix([
    [1, 2, 0, 0, 0, 1, 0, 1],
    [0, 0, 2, 2, 1, 2, 1, 0],
    [2, 2, 2, 1, 0, 1, 0, 0],
    [0, 1, 0, 1, 1, 0, 0, 0],
])

# Concrete section R : F3^4 -> F3^8 with U R = I.
R = sp.Matrix([
    [0, 0, 1, 0],
    [0, 0, 0, 2],
    [0, 1, 1, 0],
    [0, 1, 0, 2],
    [0, 0, 0, 0],
    [0, 0, 0, 0],
    [0, 0, 0, 0],
    [1, 2, 2, 0],
])

J = sp.Matrix([
    [0, 1, 0, 0],
    [2, 0, 0, 0],
    [0, 0, 0, 1],
    [0, 0, 2, 0],
])


def mod3_matrix(m: sp.Matrix) -> sp.Matrix:
    return m.applyfunc(lambda x: int(x) % P)


def rank_mod3(m: sp.Matrix) -> int:
    a = [list(map(lambda x: int(x) % P, row)) for row in m.tolist()]
    rows, cols = len(a), len(a[0])
    r = 0
    for c in range(cols):
        piv = next((i for i in range(r, rows) if a[i][c] % P), None)
        if piv is None:
            continue
        a[r], a[piv] = a[piv], a[r]
        inv = pow(a[r][c] % P, -1, P)
        a[r] = [(inv * x) % P for x in a[r]]
        for i in range(rows):
            if i != r and a[i][c] % P:
                lam = a[i][c] % P
                a[i] = [(x - lam * y) % P for x, y in zip(a[i], a[r])]
        r += 1
        if r == rows:
            break
    return r


def tuple_col(v: sp.Matrix) -> tuple[int, ...]:
    return tuple(int(v[i]) for i in range(v.rows))


def qcoord(v: tuple[int, ...] | sp.Matrix) -> tuple[int, ...]:
    col = sp.Matrix(v) if not isinstance(v, sp.Matrix) else v
    z = mod3_matrix(U * col)
    return tuple(int(z[i]) for i in range(4))


def compute_receipt() -> dict[str, object]:
    edges = ((0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (2, 7))
    gram = sp.eye(8) * 2
    for i, j in edges:
        gram[i, j] = -1
        gram[j, i] = -1

    ident = sp.eye(8)
    reflections = []
    for i in range(8):
        e = sp.zeros(8, 1)
        e[i] = 1
        reflections.append(ident - e * gram.row(i))

    coxeter = ident
    for s in reflections:
        coxeter = s * coxeter
    w = coxeter**10
    assert w**3 == ident

    one_minus_w = ident - w
    det_a = abs(int(one_minus_w.det()))
    assert det_a == 81

    a3 = mod3_matrix(one_minus_w)
    w3 = mod3_matrix(w)
    u3 = mod3_matrix(U)
    r3 = mod3_matrix(R)

    kills = mod3_matrix(u3 * a3) == sp.zeros(4, 8)
    invariant = mod3_matrix(u3 * w3) == u3
    right_inverse = mod3_matrix(u3 * r3) == sp.eye(4)
    quotient_rank = rank_mod3(u3)
    image_rank = rank_mod3(a3)

    # U has rank four, so ker(U mod 3) has 3^4 elements inside F3^8.
    # The integer kernel has index 3^4=81. Since (1-w)E8 is contained in
    # ker(U) and has the same index det(1-w)=81, the two sublattices coincide.
    kernel_index = P**quotient_rank
    equal_index = kernel_index == det_a
    same_object_kernel = kills and quotient_rank == 4 and equal_index

    # Alternating lattice form K descends through the quotient because A kills
    # it on both sides mod 3. The chosen section produces exactly the standard J.
    k = gram * (w - w**2)
    k3 = mod3_matrix(k)
    left_descends = mod3_matrix(a3.T * k3) == sp.zeros(8, 8)
    right_descends = mod3_matrix(k3 * a3) == sp.zeros(8, 8)
    descended = mod3_matrix(r3.T * k3 * r3)
    standard_symplectic = descended == J

    # Generate all 240 E8 roots from a simple root under the simple reflections.
    root0 = sp.zeros(8, 1)
    root0[0] = 1
    roots = {tuple_col(root0)}
    queue = deque([root0])
    while queue:
        root = queue.popleft()
        for s in reflections:
            nxt = s * root
            key = tuple_col(nxt)
            if key not in roots:
                roots.add(key)
                queue.append(nxt)
    assert len(roots) == 240

    class_counts = Counter(qcoord(r) for r in roots)
    assert (0, 0, 0, 0) not in class_counts
    assert len(class_counts) == 80
    assert set(class_counts.values()) == {3}

    def wact(r: tuple[int, ...]) -> tuple[int, ...]:
        return tuple_col(w * sp.Matrix(r))

    seen: set[tuple[int, ...]] = set()
    orbits: list[tuple[tuple[int, ...], ...]] = []
    each_orbit_one_class = True
    for root in roots:
        if root in seen:
            continue
        orbit = []
        x = root
        for _ in range(3):
            orbit.append(x)
            seen.add(x)
            x = wact(x)
        assert x == root and len(set(orbit)) == 3
        if len({qcoord(r) for r in orbit}) != 1:
            each_orbit_one_class = False
        orbits.append(tuple(orbit))

    orbit_classes = [qcoord(o[0]) for o in orbits]
    distinct_orbit_classes = len(set(orbit_classes)) == len(orbits) == 80

    return {
        "cartan_determinant": int(gram.det()),
        "det_one_minus_w": det_a,
        "rank_one_minus_w_mod3": image_rank,
        "quotient_map_rank": quotient_rank,
        "quotient_map_kills_one_minus_w": kills,
        "quotient_map_is_w_invariant": invariant,
        "section_is_right_inverse": right_inverse,
        "kernel_index": kernel_index,
        "image_index": det_a,
        "kernel_index_equals_image_index": equal_index,
        "same_object_kernel_identification": same_object_kernel,
        "alternating_form_descends_left": left_descends,
        "alternating_form_descends_right": right_descends,
        "descended_form": tuple(tuple(int(descended[i, j]) for j in range(4)) for i in range(4)),
        "descended_form_is_standard_symplectic": standard_symplectic,
        "root_count": len(roots),
        "nonzero_quotient_classes_hit": len(class_counts),
        "roots_per_nonzero_class": next(iter(set(class_counts.values()))),
        "order_three_orbits": len(orbits),
        "each_w_orbit_is_one_quotient_class": each_orbit_one_class,
        "distinct_orbits_give_distinct_classes": distinct_orbit_classes,
        "quotient_matrix_U": tuple(tuple(int(u3[i, j]) for j in range(8)) for i in range(4)),
        "section_matrix_R": tuple(tuple(int(r3[i, j]) for j in range(4)) for i in range(8)),
    }


if __name__ == "__main__":
    print(json.dumps(compute_receipt(), indent=2, sort_keys=True))
