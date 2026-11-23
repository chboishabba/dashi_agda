#!/usr/bin/env python3
"""Local-only SymPy regression for RH G2/369 C3-S3 determinant sufficiency.

Finite algebraic verification only. It neither imports Alpöge's external
proof nor identifies its O(2,n) automorphic determinant with the existing
RiemannG2e finite taper determinant.
"""
from itertools import permutations
from sympy import Matrix, symbols, simplify

u,v,w,a,b,c,d,e,f = symbols("u v w a b c d e f")
rows = [Matrix([[u,v,w]]), Matrix([[a,b,c]]), Matrix([[d,e,f]])]
det = Matrix.vstack(*rows).det()
assert det != 0
for perm in permutations(range(3)):
    candidate = Matrix.vstack(*[
        Matrix([[row[i] for i in perm]]) for row in rows
    ]).det()
    parity = sum(perm[i] > perm[j] for i in range(3)
                 for j in range(i+1,3))
    assert simplify(candidate - ((-1)**parity)*det) == 0

# Fixed n1,n2: response q = det(n1,n2,h) is a sufficient scalar ONLY
# for consumers of q. Other full-vector consumers can separate its fibres.
n1, n2 = Matrix([[1,0,0]]), Matrix([[0,1,0]])
h1, h2 = Matrix([[2,3,4]]), Matrix([[5,6,4]])
q1, q2 = (Matrix.vstack(n1,n2,h).det() for h in (h1,h2))
assert q1 == q2 == 4
assert 7*q1 == 7*q2
assert (h1*h1.T)[0] != (h2*h2.T)[0]
print("PASS: 6/6 exact S3 determinant parity identities")
print("PASS: cyclic C3 preserves the oriented determinant")
print("PASS: fixed-kernel determinant sufficient, full-vector norm differs")
