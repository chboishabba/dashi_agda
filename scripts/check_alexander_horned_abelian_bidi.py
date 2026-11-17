#!/usr/bin/env python3
"""Finite-stage horn-meridian abelianisation witness, NOT exterior pi1.
The linked free-group generators can have a nonidentity commutator in S3;
all abelian character images of a commutator vanish. A finite-stage S3
representation need not extend to the infinite, perfect horned group.
"""
from itertools import product

IDENTITY = (0, 1, 2)
def mul(a, b):
    return tuple(a[b[i]] for i in range(3))
def inv(a):
    return tuple(a.index(i) for i in range(3))
def comm(a, b):
    return mul(mul(mul(a, b), inv(a)), inv(b))

a, b = (1, 0, 2), (0, 2, 1)
c = comm(a, b)
assert c != IDENTITY
assert mul(mul(c, c), c) == IDENTITY
print("finite F2 stage -> S3 nonabelian commutator:", c)
for n in range(2, 20):
    for x, y in product(range(n), repeat=2):
        assert (x+y-x-y) % n == 0
print("finite abelian-character test: all commutators -> 0 in Z/n (2<=n<20)")

# Topologically equal intrinsic S2 surfaces, but distinct complement query.
standard = {"intrinsic": "S2", "complement_pi1_nontrivial": False}
horned = {"intrinsic": "S2", "complement_pi1_nontrivial": True}
assert standard["intrinsic"] == horned["intrinsic"]
assert standard["complement_pi1_nontrivial"] != horned["complement_pi1_nontrivial"]
print("intrinsic-sphere observer has a concrete ambient-complement collision")
print("PASS finite-stage illustration; the Agda no-go is conditional on its")
print("meridian presentation; no KK physical boundary or C3 wild action proved.")
