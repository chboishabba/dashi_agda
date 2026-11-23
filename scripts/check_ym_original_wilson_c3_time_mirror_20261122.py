#!/usr/bin/env python3
"""Exhaustive native side-four Wilson C3/time-mirror reference check.
The source-positive temporal link is inverted at (-t-1,x,y,z).
Finite exact geometry only: not an Agda kernel or continuum OS receipt.
"""
from itertools import product
from sympy import __version__ as sympy_version
from sympy.combinatorics import Permutation

L = 4
bonds = tuple((*s, a) for s in product(range(L), repeat=4) for a in range(L))
assert len(bonds) == 1024
positions = {bond: j for j, bond in enumerate(bonds)}

def c3(bond):
    t, x, y, z, a = bond
    return (t, z, x, y, (0, 2, 3, 1)[a])

def mirror(bond):
    t, x, y, z, a = bond
    if a == 0:
        return ((-t - 1) % L, x, y, z, a), -1
    return ((-t) % L, x, y, z, a), 1

def temporal_then_spatial(bond):
    label, sign = mirror(bond)
    return c3(label), sign

def spatial_then_temporal(bond):
    return mirror(c3(bond))

# A faithful noncommutative quaternion Q8 reference: i*j=k, j*i=-k.
units = (
    ((1, 0), (1, 1), (1, 2), (1, 3)),
    ((1, 1), (-1, 0), (1, 3), (-1, 2)),
    ((1, 2), (-1, 3), (-1, 0), (1, 1)),
    ((1, 3), (1, 2), (-1, 1), (-1, 0)),
)
def mul(left, right):
    sign, unit = units[left[1]][right[1]]
    return (left[0] * right[0] * sign, unit)

def inverse(q):
    return q if q[1] == 0 else (-q[0], q[1])

assert mul((1, 1), (1, 2)) == (1, 3)
assert mul((1, 2), (1, 1)) == (-1, 3)
assert all(mul(q, inverse(q)) == (1, 0)
           for q in product((-1, 1), range(4)))

rotation = Permutation([positions[c3(b)] for b in bonds])
reflection = Permutation([positions[mirror(b)[0]] for b in bonds])
assert rotation.order() == 3
assert reflection.order() == 2
assert rotation * reflection == reflection * rotation
checks = 3
for b in bonds:
    assert temporal_then_spatial(b) == spatial_then_temporal(b)
    checks += 1
    assert c3(c3(c3(b))) == b
    checks += 1
    bb, sign = mirror(b)
    bbb, sign2 = mirror(bb)
    assert bbb == b and sign * sign2 == 1
    checks += 1
    for q in product((-1, 1), range(4)):
        left_label, left_sign = temporal_then_spatial(b)
        right_label, right_sign = spatial_then_temporal(b)
        left_value = inverse(q) if left_sign < 0 else q
        right_value = inverse(q) if right_sign < 0 else q
        assert (left_label, left_value) == (right_label, right_value)
        checks += 1

# Time/space swaps are NOT eligible C3 rotations of the OS time mirror.
def wrong_swap(b):
    t, x, y, z, a = b
    return (x, t, y, z, (1, 0, 2, 3)[a])
assert any(
    (lambda label, sign: (wrong_swap(label), sign))(*mirror(b))
    != mirror(wrong_swap(b))
    for b in bonds
)
checks += 1
print("SymPy:", sympy_version)
print("Original positive bonds:", len(bonds))
print("Quaternion inversion probes:", len(bonds) * 8)
print("Negative control time/space swap: correctly rejected")
print("Exact checks:", checks, "/", checks, "PASS")
