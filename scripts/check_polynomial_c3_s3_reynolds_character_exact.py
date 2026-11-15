"""Exact rational C3/S3 Reynolds character regression on 27 ternary endomorphisms.

Classical finite-group representation theory. DASHI original code and executed
finite checks are distinct from historic theory and Agda kernel certification.
"""
from itertools import permutations, product
from fractions import Fraction
from collections import Counter

X = tuple(product(range(3), repeat=3))
G = tuple(permutations(range(3)))
ID, ROT, REF = (0, 1, 2), (1, 2, 0), (1, 0, 2)

def inverse(p):
    return tuple(p.index(i) for i in range(3))

def conjugate(p, f):
    q = inverse(p)
    return tuple(p[f[q[i]]] for i in range(3))

def compose(p, q):
    return tuple(p[q[i]] for i in range(3))

def apply(p, v):
    return tuple(v[X.index(conjugate(p, x))] for x in X)

def average(H, v):
    return tuple(sum((apply(p, v)[i] for p in H), Fraction()) / len(H)
                 for i in range(27))

def fixed(p):
    return sum(conjugate(p, x) == x for x in X)

def orbits(H):
    missing = set(X)
    result = []
    while missing:
        x = min(missing)
        o = frozenset(conjugate(p, x) for p in H)
        result.append(o)
        missing -= o
    return result

def main():
    C3 = (ID, ROT, compose(ROT, ROT))
    assert Counter(map(len, orbits(C3))) == {1: 3, 3: 8}
    assert Counter(map(len, orbits(G))) == {1: 1, 2: 1, 3: 2, 6: 3}
    assert (sum(map(fixed, C3)) // 3, sum(map(fixed, G)) // 6) == (11, 7)
    assert (fixed(ID), fixed(ROT), fixed(REF)) == (27, 3, 3)
    q = orbits(C3)
    assert sum(frozenset(conjugate(REF, x) for x in o) == o for o in q) == 3
    zero = tuple(Fraction(0) for _ in X)
    for seed in range(24):
        v = tuple(Fraction((i*i + seed*(i+3)) % 17 - 8, (i%5)+1)
                  for i in range(27))
        c, s = average(C3, v), average(G, v)
        assert average(C3, c) == c and average(G, s) == s
        assert average(C3, s) == s and average(G, c) == s
        refl = apply(REF, c)
        even = tuple((a+b)/2 for a,b in zip(c, refl))
        odd = tuple((a-b)/2 for a,b in zip(c, refl))
        assert even == s
        assert all(a+b == t for a,b,t in zip(even, odd, c))
        assert apply(REF, odd) == tuple(-a for a in odd)
        assert average(G, odd) == zero
    print("PASS: C3 11, S3 7, reflection-even 7, reflection-odd 4")
    print("PASS: 24 rational fields, Reynolds idempotence/absorption/decomposition")

if __name__ == "__main__":
    main()
