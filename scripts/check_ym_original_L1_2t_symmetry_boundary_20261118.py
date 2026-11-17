#!/usr/bin/env python3
"""Exact 2T symmetry audit for the ORIGINAL six-commutator L=1 model.

Independent finite algebra checks:
- 2T has seven conjugacy classes, not seven distinct real-trace classes;
- the source pair deficit is invariant under simultaneous conjugation;
- simultaneous left multiplication is NOT an action symmetry.
No claim of Agda kernel acceptance or physical RG convergence.
"""
from fractions import Fraction as Q
from itertools import product
from collections import Counter

nodes = []
for a in range(4):
    for sign in (-1, 1):
        q = [Q(0)] * 4
        q[a] = Q(sign)
        nodes.append(tuple(q))
nodes += [
    tuple(Q(sign, 2) for sign in signs)
    for signs in product((-1, 1), repeat=4)
]
assert len(nodes) == len(set(nodes)) == 24
node_set = set(nodes)

def mul(q, r):
    a, b, c, d = q
    e, f, g, h = r
    return (a*e-b*f-c*g-d*h, a*f+b*e+c*h-d*g,
            a*g-b*h+c*e+d*f, a*h+b*g-c*f+d*e)

def inverse(q):
    return (q[0], -q[1], -q[2], -q[3])

def conjugate(g, q):
    return mul(mul(g, q), inverse(g))

def pair_deficit(q, r):
    return 2 * sum(
        (q[a]*r[b]-q[b]*r[a])**2
        for a, b in ((1, 2), (1, 3), (2, 3))
    )

def action(u):
    return sum(pair_deficit(u[i], u[j])
               for i in range(4) for j in range(i+1, 4))

assert all(mul(q, r) in node_set for q in nodes for r in nodes)
assert all(inverse(q) in node_set for q in nodes)

classes = []
remaining = node_set.copy()
while remaining:
    q = min(remaining)
    orbit = {conjugate(g, q) for g in nodes}
    assert orbit <= remaining
    classes.append(orbit)
    remaining -= orbit
assert sorted(map(len, classes)) == [1, 1, 4, 4, 4, 4, 6]
assert len({next(iter(c))[0] for c in classes}) == 5
assert len(set().union(*classes)) == 24

checks = 0
for g in nodes:
    for q in nodes:
        for r in nodes:
            assert pair_deficit(conjugate(g, q), conjugate(g, r)) == pair_deficit(q, r)
            checks += 1
assert checks == 24**3

# Concrete source-action counterexample to the proposed global
# left-multiplication shortcut. S changes from 0 to 6.
minus_one = (Q(-1), Q(0), Q(0), Q(0))
minus_i = (Q(0), Q(-1), Q(0), Q(0))
minus_j = (Q(0), Q(0), Q(-1), Q(0))
u = (minus_one, minus_one, minus_one, minus_i)
left = tuple(mul(minus_j, q) for q in u)
assert action(u) == 0 and action(left) == 6

# The coarse trace observable survives simultaneous conjugation.
assert all(
    conjugate(g, mul(q, r))[0] == mul(q, r)[0]
    for g in nodes for q in nodes for r in nodes
)

print("PASS: 2T 24-node closure/inverses, 7 conjugacy classes (5 trace values),")
print(f"      {checks} diagonal-conjugation pair-deficit checks,")
print("      conjugation-invariant blocked trace and left-action counterexample 0 -> 6")
