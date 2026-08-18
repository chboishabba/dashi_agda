#!/usr/bin/env python3
"""Reproduce the finite local p=2 quotient used by the p=11 marked oldspace.

This is a verifier/falsifier, not theorem authority.

Finite compact model:
  G  = GL_2(Z/4Z), |G|=96
  B  = { matrices with c=0 mod 4 }, |B|=16
  K2 = ker(GL_2(Z/4Z) -> GL_2(F_2)), |K2|=16

On the six-point carrier B\G:
  right K2 has three 2-point orbits (the P^1(F_2) deck fibres);
  right B has orbit sizes 4,1,1 (the B\G/B Bruhat classes).

Averaging a K2-invariant function over right B gives, relative to the orbit
indicator bases, the rational matrix

    [[1/2, 1/2, 0],
     [0,   0,   1],
     [0,   0,   1]].

After clearing denominator 2 this is

    [[1,1,0],
     [0,0,2],
     [0,0,2]],

which has rank 2 and collapses the first two K2 basis vectors.  Therefore
compact averaging alone cannot identify the three-dimensional principal-level-2
fixed-vector model with the three-dimensional Gamma_0(4) oldvector model.
"""

from __future__ import annotations

from fractions import Fraction
from itertools import product
from math import gcd


Matrix = tuple[int, int, int, int]


def det(m: Matrix) -> int:
    a, b, c, d = m
    return (a * d - b * c) % 4


def mul(x: Matrix, y: Matrix) -> Matrix:
    a, b, c, d = x
    e, f, g, h = y
    return (
        (a * e + b * g) % 4,
        (a * f + b * h) % 4,
        (c * e + d * g) % 4,
        (c * f + d * h) % 4,
    )


G: list[Matrix] = [m for m in product(range(4), repeat=4) if gcd(det(m), 4) == 1]
I: Matrix = (1, 0, 0, 1)
B: list[Matrix] = [m for m in G if m[2] == 0]
K2: list[Matrix] = [m for m in G if all((x - y) % 2 == 0 for x, y in zip(m, I))]

assert len(G) == 96
assert len(B) == 16
assert len(K2) == 16

# Left cosets B\G.
unseen = set(G)
left_cosets: list[set[Matrix]] = []
which_coset: dict[Matrix, int] = {}
while unseen:
    g = next(iter(unseen))
    coset = {mul(b, g) for b in B}
    idx = len(left_cosets)
    left_cosets.append(coset)
    for x in coset:
        which_coset[x] = idx
    unseen -= coset

assert len(left_cosets) == 6
assert all(len(c) == 16 for c in left_cosets)
representatives = [next(iter(c)) for c in left_cosets]


def right_action(i: int, h: Matrix) -> int:
    return which_coset[mul(representatives[i], h)]


def right_orbits(subgroup: list[Matrix]) -> list[list[int]]:
    remaining = set(range(len(left_cosets)))
    out: list[list[int]] = []
    while remaining:
        i = next(iter(remaining))
        orbit = sorted({right_action(i, h) for h in subgroup})
        out.append(orbit)
        remaining -= set(orbit)
    return out


k2_orbits = right_orbits(K2)
b_orbits = right_orbits(B)

assert sorted(map(len, k2_orbits)) == [2, 2, 2]
assert sorted(map(len, b_orbits)) == [1, 1, 4]

# Normalize orbit ordering deterministically by size then lexicographic index.
k2_orbits = sorted(k2_orbits)
b_orbits = sorted(b_orbits, key=lambda xs: (-len(xs), xs))

# Right-B averaging of K2-orbit indicator functions, read on one representative
# of each B orbit.
averaging: list[list[Fraction]] = []
for b_orbit in b_orbits:
    source = b_orbit[0]
    row: list[Fraction] = []
    for k_orbit in k2_orbits:
        hits = sum(1 for h in B if right_action(source, h) in k_orbit)
        row.append(Fraction(hits, len(B)))
    averaging.append(row)

expected = [
    [Fraction(1, 2), Fraction(1, 2), Fraction(0, 1)],
    [Fraction(0, 1), Fraction(0, 1), Fraction(1, 1)],
    [Fraction(0, 1), Fraction(0, 1), Fraction(1, 1)],
]
assert averaging == expected, (k2_orbits, b_orbits, averaging)

cleared = [[2 * x for x in row] for row in averaging]
assert cleared == [
    [Fraction(1), Fraction(1), Fraction(0)],
    [Fraction(0), Fraction(0), Fraction(2)],
    [Fraction(0), Fraction(0), Fraction(2)],
]

# Exact rank over Q.
def rank_q(matrix: list[list[Fraction]]) -> int:
    a = [row[:] for row in matrix]
    rows, cols = len(a), len(a[0])
    r = 0
    for c in range(cols):
        pivot = next((i for i in range(r, rows) if a[i][c] != 0), None)
        if pivot is None:
            continue
        a[r], a[pivot] = a[pivot], a[r]
        p = a[r][c]
        a[r] = [x / p for x in a[r]]
        for i in range(rows):
            if i == r:
                continue
            q = a[i][c]
            if q:
                a[i] = [x - q * y for x, y in zip(a[i], a[r])]
        r += 1
    return r


assert rank_q(averaging) == 2
# e1-e2 is an explicit kernel vector.
assert all(row[0] - row[1] == 0 for row in averaging)

print("|GL2(Z/4)| =", len(G))
print("|B| = |K(2)| =", len(B))
print("K(2) orbit sizes on B\\G:", [len(x) for x in k2_orbits])
print("B orbit sizes on B\\G:", [len(x) for x in b_orbits])
print("B-averaging matrix:")
for row in averaging:
    print(" ", row)
print("rank =", rank_q(averaging))
print("verified: compact averaging collapses e1-e2 and is not an isomorphism")
