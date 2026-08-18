#!/usr/bin/env python3
"""Deterministically identify Schmidt's n=2 Casselman cells mod 4.

This is an executable verifier, not theorem authority.

Schmidt Lemma 2.1.1 uses representatives gamma_i whose nonterminal cells are
characterized by v(c)=i.  For n=2 we use

    gamma_0 = [[1,0],[1,1]],
    gamma_1 = [[1,0],[2,1]],
    gamma_2 = I,

where gamma_2 represents the terminal c == 0 mod 4 cell.

On B(Z/4)\GL_2(Z/4), canonical left-coset ordering gives right-B orbits

    {0,1,2,3}, {4}, {5}.

The gamma representatives lie in cosets 1,5,4 respectively.  Hence the
Bruhat3 row order used by verify_p11_two_adic_local_averaging.py is

    wide  = valuation0,
    left  = terminal2,
    right = valuation1.
"""

from __future__ import annotations

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


G = [m for m in product(range(4), repeat=4) if gcd(det(m), 4) == 1]
B = [m for m in G if m[2] == 0]

assert len(G) == 96
assert len(B) == 16

# Canonical B-left-coset order: repeatedly choose the lexicographically least
# remaining matrix, then sort completed cosets by their least representative.
unseen = set(G)
left_cosets: list[set[Matrix]] = []
while unseen:
    g = min(unseen)
    coset = {mul(b, g) for b in B}
    left_cosets.append(coset)
    unseen -= coset
left_cosets.sort(key=lambda c: min(c))

assert len(left_cosets) == 6

which_coset: dict[Matrix, int] = {}
for i, coset in enumerate(left_cosets):
    for g in coset:
        which_coset[g] = i

representatives = [min(c) for c in left_cosets]


def right_action(i: int, h: Matrix) -> int:
    return which_coset[mul(representatives[i], h)]


def right_orbits(subgroup: list[Matrix]) -> list[list[int]]:
    remaining = set(range(6))
    result: list[list[int]] = []
    while remaining:
        i = min(remaining)
        orbit = sorted({right_action(i, h) for h in subgroup})
        result.append(orbit)
        remaining -= set(orbit)
    return result


b_orbits = sorted(right_orbits(B), key=lambda xs: (-len(xs), xs))
assert b_orbits == [[0, 1, 2, 3], [4], [5]]

gamma0: Matrix = (1, 0, 1, 1)
gamma1: Matrix = (1, 0, 2, 1)
gamma2: Matrix = (1, 0, 0, 1)

assert which_coset[gamma0] == 1
assert which_coset[gamma1] == 5
assert which_coset[gamma2] == 4

assert which_coset[gamma0] in b_orbits[0]
assert which_coset[gamma2] in b_orbits[1]
assert which_coset[gamma1] in b_orbits[2]

print("canonical B\\G representatives:")
for i, rep in enumerate(representatives):
    print(i, rep)
print("right-B orbits:", b_orbits)
print("gamma_0 coset:", which_coset[gamma0], "-> wide / valuation0")
print("gamma_1 coset:", which_coset[gamma1], "-> right / valuation1")
print("gamma_2 coset:", which_coset[gamma2], "-> left / terminal2")
print("verified Bruhat3 order: (wide,left,right)=(valuation0,terminal2,valuation1)")
