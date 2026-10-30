#!/usr/bin/env python3
"""Finite exact arithmetic checks for PolynomialMonodromyTernaryQuaternionBridgeExact.

This checks the mathematical values independently using Python permutations
and exact rational quaternions. It is NOT an Agda kernel receipt.
"""
from fractions import Fraction as F
from itertools import permutations, product

def compose(left, right):
    return tuple(left[right[x]] for x in range(3))

def invert(p):
    return tuple(p.index(i) for i in range(3))

def commutator(a, b):
    return compose(compose(compose(a, b), invert(a)), invert(b))

I = (0, 1, 2)
A = (1, 0, 2)  # swap first and second
B = (0, 2, 1)  # swap second and third
R = (1, 2, 0)
R2 = (2, 0, 1)
S3 = set(permutations(range(3)))
assert len(S3) == 6
assert compose(compose(A, B), A) == compose(compose(B, A), B)
assert commutator(A, B) == R2
assert compose(compose(R, R), R) == I
assert len({I, R, R2}) == 3
assert A not in {I, R, R2}
assert all(compose(p, invert(p)) == I for p in S3)

# All 36 pairwise commutators lie in C3, and their commutators are trivial.
derived = {commutator(a, b) for a, b in product(S3, repeat=2)}
assert derived == {I, R, R2}, derived
assert all(commutator(a, b) == I for a, b in product(derived, repeat=2))

def qmul(a, b):
    w, x, y, z = a
    u, v, s, t = b
    return (
        w*u-x*v-y*s-z*t,
        w*v+x*u+y*t-z*s,
        w*s-x*t+y*u+z*v,
        w*t+x*s-y*v+z*u,
    )

def conjugate(q):
    return (q[0], -q[1], -q[2], -q[3])

one = (F(1), F(0), F(0), F(0))
minus_one = (F(-1), F(0), F(0), F(0))
q = (F(1, 2), F(1, 2), F(1, 2), F(1, 2))
assert sum(x*x for x in q) == 1
q2 = qmul(q, q)
q3 = qmul(q2, q)
q6 = qmul(q3, q3)
assert q3 == minus_one
assert q6 == one
axis = [
    (F(0), F(1), F(0), F(0)),
    (F(0), F(0), F(1), F(0)),
    (F(0), F(0), F(0), F(1)),
]
for index in range(3):
    assert qmul(qmul(q, axis[index]), conjugate(q)) == axis[R[index]]

# Explicitly separate alphabet-count and root-label combinatorics.
trit_five = list(product((-1, 0, 1), repeat=5))
mode_three = list(product(range(5), repeat=3))
distinct_root_triples = [
    x for x in mode_three if len(set(x)) == 3
]
assert len(trit_five) == 3**5 == 243
assert len(mode_three) == 5**3 == 125
assert len(distinct_root_triples) == 60
assert 3**5 != 5**3
print("MONODROMY_TERNARY_SPIN_FINITE PASS "
      "s3=6 commutator_subgroup=3 second_derived=1 "
      "trit5=243 mode5_triples=125 no_replacement=60 "
      "quaternion_q3=-1 q6=+1 basis_cycle=3")
