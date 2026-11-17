#!/usr/bin/env python3
"""Exact F2 counterexample: three cyclic Tate defects do not determine double Tate.

We exhibit two 5-dimensional representations of V4 via commuting square-zero
operators A,H (generators are 1+A and 1+H).  In both examples
K = A + H + A H = (1+A)(1+H)-1 has the same cyclic Tate-defect profile

    (dim Hhat0(A), dim Hhat0(H), dim Hhat0(K)) = (3,1,1),

but the induced H-action on Hhat0(A)=ker A / im A has different Tate defects:
1 versus 3.  Hence cyclic Tate dimensions, even for all three nontrivial V4
elements, do not determine the iterated Tate extension invariant.
"""
from __future__ import annotations


def mm(A, B):
    n = len(A)
    return [[sum(A[i][k] * B[k][j] for k in range(n)) & 1 for j in range(n)] for i in range(n)]


def add(*ms):
    return [[sum(m[i][j] for m in ms) & 1 for j in range(len(ms[0]))] for i in range(len(ms[0]))]


def rank(A):
    a = [row[:] for row in A]
    m, n = len(a), len(a[0]) if a else 0
    r = 0
    for c in range(n):
        p = next((i for i in range(r, m) if a[i][c]), None)
        if p is None:
            continue
        a[r], a[p] = a[p], a[r]
        for i in range(m):
            if i != r and a[i][c]:
                a[i] = [x ^ y for x, y in zip(a[i], a[r])]
        r += 1
    return r


def nullspace(A):
    a = [row[:] for row in A]
    m, n = len(a), len(a[0])
    pivots = []
    r = 0
    for c in range(n):
        p = next((i for i in range(r, m) if a[i][c]), None)
        if p is None:
            continue
        a[r], a[p] = a[p], a[r]
        for i in range(m):
            if i != r and a[i][c]:
                a[i] = [x ^ y for x, y in zip(a[i], a[r])]
        pivots.append(c)
        r += 1
    free = [c for c in range(n) if c not in pivots]
    out = []
    for f in free:
        x = [0] * n
        x[f] = 1
        for i in range(len(pivots) - 1, -1, -1):
            c = pivots[i]
            x[c] = sum(a[i][j] * x[j] for j in range(c + 1, n)) & 1
        out.append(x)
    return out


def transpose(A):
    return [list(x) for x in zip(*A)]


def mat_vec(A, v):
    return [sum(A[i][j] * v[j] for j in range(len(v))) & 1 for i in range(len(A))]


def colspace(A):
    cols = transpose(A)
    basis = []
    r = 0
    for v in cols:
        rr = rank(basis + [v])
        if rr > r:
            basis.append(v)
            r = rr
    return basis


def quotient_induced_rank(A, H):
    ker = nullspace(A)
    im = colspace(A)
    span = im[:]
    r = rank(span)
    q = []
    for v in ker:
        if rank(span + [v]) > r:
            q.append(v)
            span.append(v)
            r += 1
    imgs = [mat_vec(H, v) for v in q]
    return rank(im + imgs) - rank(im), len(q)


def defect(N):
    return len(N) - 2 * rank(N)


EXAMPLES = [
    (
        1,
        [[1,0,1,0,0],[1,0,1,0,0],[1,0,1,0,0],[0,0,0,0,0],[1,0,1,0,0]],
        [[0,0,1,0,1],[0,0,0,0,0],[0,0,1,0,1],[1,0,1,0,0],[0,0,1,0,1]],
    ),
    (
        3,
        [[0,1,0,0,0],[0,0,0,0,0],[0,1,0,0,0],[0,1,0,0,0],[0,0,0,0,0]],
        [[0,0,0,0,1],[0,0,0,0,0],[0,1,0,0,1],[0,0,0,0,1],[0,0,0,0,0]],
    ),
]

for expected_iterated, A, H in EXAMPLES:
    Z = [[0]*5 for _ in range(5)]
    assert mm(A,A) == Z
    assert mm(H,H) == Z
    assert mm(A,H) == mm(H,A)
    K = add(A,H,mm(A,H))
    assert mm(K,K) == Z
    cyclic = (defect(A), defect(H), defect(K))
    assert cyclic == (3,1,1), cyclic
    rbar, qdim = quotient_induced_rank(A,H)
    iterated = qdim - 2*rbar
    assert qdim == 3
    assert iterated == expected_iterated, (iterated, expected_iterated)
    print({"cyclic": cyclic, "H0_A_dimension": qdim, "induced_H_rank": rbar, "iterated_defect": iterated})

print("PASS: identical cyclic Tate profile (3,1,1), distinct iterated defects 1 and 3")
