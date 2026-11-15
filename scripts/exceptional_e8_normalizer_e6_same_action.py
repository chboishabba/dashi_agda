#!/usr/bin/env python3
from __future__ import annotations

import itertools
import json
from collections import deque
import numpy as np

P = 3
NORMALIZER_WORD = (0, 1, 0, 2, 1, 0, 4, 5, 4, 6, 5, 4)
CENTRALIZER_WORD_A = (2, 7, 1, 2, 4, 1, 4, 3, 4, 7)
CENTRALIZER_WORD_B = (5, 3, 4, 2, 6, 2, 7, 4, 1, 7, 0, 1, 0, 5, 2, 7, 5, 3, 7, 5, 2, 6, 5, 4, 5, 7, 6, 5)

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

B_E6 = np.array([
    [2,2,0,0,0],
    [2,2,2,0,2],
    [0,2,2,2,0],
    [0,0,2,2,0],
    [0,2,0,0,2],
], dtype=int) % P
M_PLUCKER_TO_E6 = np.array([
    [0,0,1,1,2],
    [0,0,0,0,1],
    [0,1,0,0,2],
    [1,2,1,2,1],
    [1,0,2,1,2],
], dtype=int) % P
E6_SIMPLE_ROOTS = (
    (1,0,0,0,0),
    (0,1,0,0,0),
    (0,0,1,0,0),
    (0,0,0,1,0),
    (0,0,0,0,1),
    (0,0,2,1,1),
)


def key(m: np.ndarray) -> tuple[int, ...]:
    return tuple(int(x) for x in m.reshape(-1))


def canon(v) -> tuple[int, ...]:
    v = tuple(int(x) % P for x in v)
    for a in v:
        if a:
            inv = 1 if a == 1 else 2
            return tuple((inv * x) % P for x in v)
    raise ValueError("zero has no projective representative")


def compose_perm(p, q):
    return tuple(p[q[i]] for i in range(len(q)))


def generated_perm_group(gens):
    identity = tuple(range(len(gens[0])))
    seen = {identity}
    queue = deque([identity])
    while queue:
        g = queue.popleft()
        for s in gens:
            h = compose_perm(s, g)
            if h not in seen:
                seen.add(h)
                queue.append(h)
    return seen


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


def induced4(g):
    return (U @ (g % P) @ R) % P


def symplectic(u, v):
    return (u[0]*v[1] - u[1]*v[0] + u[2]*v[3] - u[3]*v[2]) % P


def symplectic_lines():
    points = sorted({canon(v) for v in itertools.product(range(P), repeat=4) if any(v)})
    out = set()
    for a,b in itertools.combinations(points, 2):
        if symplectic(a,b) != 0:
            continue
        line = set()
        for x,y in itertools.product(range(P), repeat=2):
            v = tuple((x*a[i] + y*b[i]) % P for i in range(4))
            if any(v):
                line.add(canon(v))
        if len(line) == 4:
            out.add(frozenset(line))
    return sorted(out, key=lambda s: sorted(s))


def act_line4(a, line):
    return frozenset(canon((a @ np.array(p, dtype=int)) % P) for p in line)


def plucker(line):
    pts = [np.array(p, dtype=int) for p in line]
    u = pts[0]
    v = next(x for x in pts[1:] if canon(x) != canon(u))
    p = (
        u[0]*v[1] - u[1]*v[0],
        u[0]*v[2] - u[2]*v[0],
        u[0]*v[3] - u[3]*v[0],
        u[1]*v[2] - u[2]*v[1],
        u[1]*v[3] - u[3]*v[1],
        u[2]*v[3] - u[3]*v[2],
    )
    return canon(p)


def line_to_e6_null(line):
    p = plucker(line)
    assert (p[0] + p[5]) % P == 0
    return canon((M_PLUCKER_TO_E6 @ np.array(p[:5], dtype=int)) % P)


def e6_null_points():
    pts = sorted({canon(v) for v in itertools.product(range(P), repeat=5) if any(v)})
    return [p for p in pts if int(np.array(p) @ B_E6 @ np.array(p)) % P == 0]


def e6_reflection(root):
    r = np.array(root, dtype=int).reshape(5,1)
    return (np.eye(5, dtype=int) - r @ (r.T @ B_E6)) % P


def compute_receipt():
    _, reflections, w = e8_data()
    ident8 = np.eye(8, dtype=int)
    assert np.array_equal(np.linalg.matrix_power(w,3), ident8)

    n = eval_word(NORMALIZER_WORD, reflections)
    assert np.array_equal(n @ w @ np.linalg.inv(n).astype(int), w @ w)
    n4 = induced4(n)
    assert np.array_equal((n4.T @ J @ n4) % P, (2 * J) % P)

    a4 = induced4(eval_word(CENTRALIZER_WORD_A, reflections))
    b4 = induced4(eval_word(CENTRALIZER_WORD_B, reflections))
    assert np.array_equal((a4.T @ J @ a4) % P, J)
    assert np.array_equal((b4.T @ J @ b4) % P, J)

    lines = symplectic_lines()
    assert len(lines) == 40
    line_index = {line:i for i,line in enumerate(lines)}

    def line_perm(a):
        return tuple(line_index[act_line4(a, line)] for line in lines)

    e8_line_group = generated_perm_group((line_perm(a4), line_perm(b4), line_perm(n4)))
    assert len(e8_line_group) == 51840

    nulls = e6_null_points()
    assert len(nulls) == 40
    null_index = {p:i for i,p in enumerate(nulls)}
    phi = tuple(null_index[line_to_e6_null(line)] for line in lines)
    assert len(set(phi)) == 40

    def conjugate_to_null(p):
        q = [None] * 40
        for i in range(40):
            q[phi[i]] = phi[p[i]]
        return tuple(q)

    e8_on_null = {conjugate_to_null(p) for p in e8_line_group}

    def null_perm(a):
        return tuple(null_index[canon((a @ np.array(p, dtype=int)) % P)] for p in nulls)

    e6_generators = tuple(null_perm(e6_reflection(r)) for r in E6_SIMPLE_ROOTS)
    e6_group = generated_perm_group(e6_generators)
    assert len(e6_group) == 51840

    same = e8_on_null == e6_group
    assert same

    # Phase action of the normalizer is inversion on <w>.
    wpowers = (ident8, w, w @ w)
    phase_conjugation = []
    ninv = np.linalg.inv(n).astype(int)
    for p in wpowers:
        y = n @ p @ ninv
        phase_conjugation.append(next(i for i,q in enumerate(wpowers) if np.array_equal(y,q)))
    assert tuple(phase_conjugation) == (0,2,1)

    return {
        "normalizer_word": NORMALIZER_WORD,
        "normalizer_conjugates_w_to_w2": True,
        "phase_conjugation_permutation_I_w_w2": tuple(phase_conjugation),
        "normalizer_transport_matrix": n4.tolist(),
        "normalizer_multiplier": 2,
        "symplectic_line_count": len(lines),
        "e8_normalizer_projective_group_order": len(e8_line_group),
        "e6_null_group_order": len(e6_group),
        "plucker_bijection_size": len(set(phi)),
        "same_ordered_carrier_used": True,
        "permutation_sets_compared_extensionally": True,
        "permutation_sets_literally_equal": same,
    }


if __name__ == "__main__":
    print(json.dumps(compute_receipt(), indent=2, sort_keys=True))
