#!/usr/bin/env python3
"""Exact F3-linearised B4 incidence projections for the Round56 rank-two cells.

Maps the 96-dimensional F3 permutation module onto:
  - standard F4 long-root24 permutation module (rank 24);
  - standard F4 half-root16 permutation module (rank 16).
Joint map into 40 coordinates has rank 39 and 57-dimensional kernel.
This is NOT an invertible 96-to-96 F4 two-copy map, E6-folded action
identification, Albert recognition, or a certificate of physical invariance.
"""
from itertools import product
from collections import deque

def cells():
    return sorted(v for v in product((-2, -1, 1, 2), repeat=4)
                  if sum(abs(x) == 2 for x in v) == 2)

def long(v):
    return tuple(x if abs(x) == 2 else 0 for x in v)

def half(v):
    return tuple(1 if x > 0 else -1 for x in v)

def flip(v, i):
    w = list(v)
    w[i] = -w[i]
    return tuple(w)

def swap(v, i):
    w = list(v)
    w[i], w[i + 1] = w[i + 1], w[i]
    return tuple(w)

def rank_mod3(rows):
    a = [[x % 3 for x in row] for row in rows]
    m, n, pivot = len(a), len(a[0]), 0
    for j in range(n):
        pos = next((i for i in range(pivot, m) if a[i][j]), None)
        if pos is None:
            continue
        a[pos], a[pivot] = a[pivot], a[pos]
        if a[pivot][j] == 2:
            a[pivot] = [(2*x) % 3 for x in a[pivot]]
        for i in range(m):
            if i != pivot and a[i][j]:
                factor = a[i][j]
                a[i] = [(u-factor*v) % 3 for u,v in zip(a[i], a[pivot])]
        pivot += 1
        if pivot == m:
            break
    return pivot

def run():
    cs = cells()
    ls = sorted({long(c) for c in cs})
    hs = sorted({half(c) for c in cs})
    assert (len(cs), len(ls), len(hs)) == (96, 24, 16)

    L = [[int(long(c) == l) for c in cs] for l in ls]
    H = [[int(half(c) == h) for c in cs] for h in hs]
    A = L + H
    assert rank_mod3(L) == 24
    assert rank_mod3(H) == 16
    assert rank_mod3(A) == 39
    assert all(sum(row) == 4 for row in L)
    assert all(sum(row) == 6 for row in H)

    gs = ([lambda v, i=i:flip(v,i) for i in range(4)] +
          [lambda v, i=i:swap(v,i) for i in range(3)])
    cl = {c:i for i,c in enumerate(cs)}
    li = {l:i for i,l in enumerate(ls)}
    hi = {h:i for i,h in enumerate(hs)}
    for g in gs:
        for c in cs:
            gc = g(c)
            assert long(gc) == g(long(c))
            assert half(gc) == g(half(c))
            assert L[li[g(long(c))]][cl[gc]] == 1
            assert H[hi[g(half(c))]][cl[gc]] == 1

    neighbors = [set() for _ in range(40)]
    for c in cs:
        i,j = li[long(c)], 24+hi[half(c)]
        neighbors[i].add(j)
        neighbors[j].add(i)
    visited, queue = {0}, deque([0])
    while queue:
        for j in neighbors[queue.popleft()]:
            if j not in visited:
                visited.add(j)
                queue.append(j)
    assert len(visited) == 40

    print("PASS F3: long rank 24, half rank 16, combined rank 39; source kernel 57")
    print("PASS: independent 7 B4 generator coordinate actions commute with both projections")
    print("PASS: connected bipartite incidence graph with 40 vertices, 96 edges; degrees 4 and 6")
    print("LIMIT: folded F4/W(F4) action recognition, physical integrand and global root mapping open")

if __name__ == "__main__":
    run()
