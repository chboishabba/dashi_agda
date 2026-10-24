#!/usr/bin/env python3
from __future__ import annotations

import itertools
import json
from collections import deque
import numpy as np

P = 3
B = np.array([
    [2,2,0,0,0],
    [2,2,2,0,2],
    [0,2,2,2,0],
    [0,0,2,2,0],
    [0,2,0,0,2],
], dtype=int) % P
SIMPLE_ROOTS = (
    (1,0,0,0,0),
    (0,1,0,0,0),
    (0,0,1,0,0),
    (0,0,0,1,0),
    (0,0,0,0,1),
    (0,0,2,1,1),
)


def canon(v):
    v = tuple(int(x) % P for x in v)
    for a in v:
        if a:
            inv = 1 if a == 1 else 2
            return tuple((inv*x) % P for x in v)
    raise ValueError


def bilinear(u,v):
    return int(np.array(u) @ B @ np.array(v)) % P


def rref_subspaces_3d():
    for pivots in itertools.combinations(range(5),3):
        base = np.zeros((3,5), dtype=int)
        for i,p in enumerate(pivots):
            base[i,p] = 1
        nonp = [j for j in range(5) if j not in pivots]
        free = [(i,j) for i,p in enumerate(pivots) for j in nonp if j > p]
        for vals in itertools.product(range(P), repeat=len(free)):
            a = base.copy()
            for (i,j),v in zip(free,vals):
                a[i,j] = v
            yield a


def projective_lines_of_subspace(a):
    out = set()
    for coeffs in itertools.product(range(P), repeat=3):
        if coeffs == (0,0,0):
            continue
        v = sum((coeffs[i] * a[i] for i in range(3)), np.zeros(5, dtype=int)) % P
        out.add(canon(v))
    return frozenset(out)


def reflection(root):
    r = np.array(root, dtype=int).reshape(5,1)
    return (np.eye(5, dtype=int) - r @ (r.T @ B)) % P


def key(a):
    return tuple(int(x) for x in a.reshape(-1))


def matrix_group(gens):
    ident = np.eye(5, dtype=int)
    seen = {key(ident): ident}
    queue = deque([ident])
    while queue:
        g = queue.popleft()
        for s in gens:
            h = (s @ g) % P
            k = key(h)
            if k not in seen:
                seen[k] = h
                queue.append(h)
    return list(seen.values())


def act_line(g,p):
    return canon((g @ np.array(p,dtype=int)) % P)


def act_subspace(g,s):
    return frozenset(act_line(g,p) for p in s)


def compute_receipt():
    points = sorted({canon(v) for v in itertools.product(range(P), repeat=5) if any(v)})
    nulls = {p for p in points if bilinear(p,p) == 0}
    roots = {p for p in points if bilinear(p,p) == 2}
    assert (len(nulls),len(roots)) == (40,36)

    h3 = []
    for a in rref_subspaces_3d():
        s = projective_lines_of_subspace(a)
        if sum(p in roots for p in s) == 6 and sum(p in nulls for p in s) == 1:
            h3.append(s)
    assert len(h3) == 120

    by_null = {}
    for s in h3:
        q = next(p for p in s if p in nulls)
        by_null.setdefault(q,[]).append(s)
    assert len(by_null) == 40
    assert {len(v) for v in by_null.values()} == {3}

    gens = [reflection(r) for r in SIMPLE_ROOTS]
    weyl = matrix_group(gens)
    assert len(weyl) == 51840

    q0 = sorted(by_null)[0]
    fibre = by_null[q0]
    index = {s:i for i,s in enumerate(fibre)}
    stabilizer = [g for g in weyl if act_line(g,q0) == q0]
    assert len(stabilizer) == 1296

    image = set()
    for g in stabilizer:
        image.add(tuple(index[act_subspace(g,s)] for s in fibre))
    assert len(image) == 6
    assert image == set(itertools.permutations(range(3)))

    return {
        "base_null_a2cube_classes": len(by_null),
        "h3_patch_count": len(h3),
        "patches_per_base_class": 3,
        "chosen_base_stabilizer_order": len(stabilizer),
        "three_patch_permutation_image_order": len(image),
        "three_patch_permutation_image_is_full_s3": True,
        "canonical_c3_orientation_from_e6_carrier": False,
    }


if __name__ == "__main__":
    print(json.dumps(compute_receipt(), indent=2, sort_keys=True))
