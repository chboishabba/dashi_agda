#!/usr/bin/env python3
from __future__ import annotations

import json
from collections import deque
import numpy as np

P = 3
E8_DEGREES = (2, 8, 12, 14, 18, 20, 24, 30)
WORD_A = (2, 7, 1, 2, 4, 1, 4, 3, 4, 7)
WORD_B = (5, 3, 4, 2, 6, 2, 7, 4, 1, 7, 0, 1, 0, 5, 2, 7, 5, 3, 7, 5, 2, 6, 5, 4, 5, 7, 6, 5)
U = np.array([
    [1,2,0,0,0,1,0,1],
    [0,0,2,2,1,2,1,0],
    [2,2,2,1,0,1,0,0],
    [0,1,0,1,1,0,0,0],
], dtype=int) % P
R = np.array([
    [0,1,2,2],
    [2,1,2,2],
    [2,0,2,1],
    [1,2,1,2],
    [0,0,0,0],
    [0,0,0,0],
    [0,0,0,0],
    [0,0,0,0],
], dtype=int) % P
J = np.array([
    [0,1,0,0],
    [2,0,0,0],
    [0,0,0,1],
    [0,0,2,0],
], dtype=int)


def key(m: np.ndarray) -> tuple[int, ...]:
    return tuple(int(x) for x in m.reshape(-1))


def e8_data():
    edges = ((0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(2,7))
    gram = np.eye(8, dtype=int) * 2
    for i,j in edges:
        gram[i,j] = gram[j,i] = -1
    ident = np.eye(8, dtype=int)
    reflections = []
    for i in range(8):
        e = np.zeros((8,1), dtype=int)
        e[i,0] = 1
        reflections.append(ident - e @ gram[i:i+1,:])
    coxeter = ident.copy()
    for s in reflections:
        coxeter = s @ coxeter
    w = np.linalg.matrix_power(coxeter, 10)
    return gram, reflections, w


def eval_word(word, reflections):
    g = np.eye(8, dtype=int)
    for i in word:
        g = reflections[i] @ g
    return g


def induced(g):
    return (U @ (g % P) @ R) % P


def generated_group(gens, n, mod=None, limit=None):
    ident = np.eye(n, dtype=int)
    seen = {key(ident): ident}
    queue = deque([ident])
    while queue:
        x = queue.popleft()
        for s in gens:
            y = s @ x
            if mod is not None:
                y %= mod
            k = key(y)
            if k not in seen:
                seen[k] = y
                queue.append(y)
                if limit is not None and len(seen) >= limit:
                    return seen, False
    return seen, True


def compute_receipt():
    gram, reflections, w = e8_data()
    ident8 = np.eye(8, dtype=int)
    assert np.array_equal(np.linalg.matrix_power(w,3), ident8)

    # Conjugacy orbit gives the full centralizer order by orbit-stabilizer.
    orbit = {key(w): w}
    queue = deque([w])
    while queue:
        x = queue.popleft()
        for s in reflections:
            y = s @ x @ s
            k = key(y)
            if k not in orbit:
                orbit[k] = y
                queue.append(y)
    weyl_order = int(np.prod(E8_DEGREES))
    assert len(orbit) == 4480
    assert weyl_order == 696729600
    centralizer_order = weyl_order // len(orbit)
    assert centralizer_order == 155520

    ga = eval_word(WORD_A, reflections)
    gb = eval_word(WORD_B, reflections)
    assert np.array_equal(ga @ w, w @ ga)
    assert np.array_equal(gb @ w, w @ gb)

    aa, ab = induced(ga), induced(gb)
    assert np.array_equal((aa.T @ J @ aa) % P, J)
    assert np.array_equal((ab.T @ J @ ab) % P, J)

    image, image_complete = generated_group((aa,ab), 4, mod=P, limit=60000)
    assert image_complete and len(image) == 51840

    lift, lift_complete = generated_group((ga,gb,w), 8, limit=160000)
    assert lift_complete and len(lift) == 155520

    ident4 = np.eye(4, dtype=int)
    kernel = []
    image_keys = set()
    fibres = {}
    for g in lift.values():
        a = induced(g)
        ka = key(a)
        image_keys.add(ka)
        fibres[ka] = fibres.get(ka,0) + 1
        if np.array_equal(a, ident4):
            kernel.append(g)
    assert len(image_keys) == 51840
    assert set(fibres.values()) == {3}
    assert len(kernel) == 3
    wpowers = [ident8, w, w @ w]
    assert all(any(np.array_equal(k,p) for p in wpowers) for k in kernel)

    return {
        "e8_weyl_order": weyl_order,
        "conjugacy_orbit_size": len(orbit),
        "centralizer_order_orbit_stabilizer": centralizer_order,
        "explicit_generator_word_a": WORD_A,
        "explicit_generator_word_b": WORD_B,
        "both_words_commute_with_w": True,
        "transport_generator_a": aa.tolist(),
        "transport_generator_b": ab.tolist(),
        "transport_generators_are_symplectic": True,
        "transport_image_order": len(image_keys),
        "expected_sp4_3_order": 51840,
        "lift_generated_order": len(lift),
        "lift_is_full_centralizer_by_order": len(lift) == centralizer_order,
        "kernel_order": len(kernel),
        "kernel_is_exactly_w_cyclic": True,
        "all_transport_fibres_size": next(iter(set(fibres.values()))),
        "exact_sequence_computationally_closed": True,
    }


if __name__ == "__main__":
    print(json.dumps(compute_receipt(), indent=2, sort_keys=True))
