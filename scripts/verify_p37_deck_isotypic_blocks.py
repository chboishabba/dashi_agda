#!/usr/bin/env python3
"""Exact finite verifier for the p=37 marked deck-isotypic Hecke blocks.

This script independently regenerates the block matrices encoded in
P37MarkedDeckIsotypicJointDecompositionExact.agda from the orbital specs in
P37MarkedX2DeckOrbitalHeckeExact.agda.

No Sage/SymPy dependency is required.  All arithmetic is integral.
"""

from fractions import Fraction

# TriPermutation labels in the same low/mid/high convention as the Agda files.
I = "I"
R = "R"
R2 = "R2"
SMH = "SMH"
SLM = "SLM"
SLH = "SLH"

PERM = {
    I: (0, 1, 2),
    R: (1, 2, 0),
    R2: (2, 0, 1),
    SMH: (0, 2, 1),
    SLM: (1, 0, 2),
    SLH: (2, 1, 0),
}
SIGN = {I: 1, R: 1, R2: 1, SMH: -1, SLM: -1, SLH: -1}

# Standard multiplicity representation on the right-S-fixed, zero-average
# frame slice (u+v,-u,-v,u+v,-u,-v), derived from actual left frame action.
STD = {
    I: ((1, 0), (0, 1)),
    R: ((0, 1), (-1, -1)),
    R2: ((-1, -1), (1, 0)),
    SMH: ((0, 1), (1, 0)),
    SLM: ((-1, -1), (0, 1)),
    SLH: ((1, 0), (-1, -1)),
}

T3_SPECS = [
    (SMH, (SLM, I, I)),
    (SMH, (SLM, SMH, SMH)),
    (R, (SMH, SLH, R)),
    (R2, (R2, SMH, SLH)),
]
T5_SPECS = [
    (SMH, (R, SMH, SLM)),
    (SMH, (R2, SLM, SMH)),
    (SLM, (I, I, SLH)),
    (R, (SLH, SLM, R2)),
    (R2, (R, SLH, SLM)),
    (SLH, (SLM, SLH, SLM)),
]


def zeros(n, m=None):
    if m is None:
        m = n
    return [[0 for _ in range(m)] for _ in range(n)]


def eye(n):
    out = zeros(n)
    for i in range(n):
        out[i][i] = 1
    return out


def add(a, b):
    return [[a[i][j] + b[i][j] for j in range(len(a[0]))] for i in range(len(a))]


def scale(c, a):
    return [[c * x for x in row] for row in a]


def mul(a, b):
    return [
        [sum(a[i][k] * b[k][j] for k in range(len(b))) for j in range(len(b[0]))]
        for i in range(len(a))
    ]


def matvec(a, v):
    return [sum(a[i][j] * v[j] for j in range(len(v))) for i in range(len(a))]


def power(a, n):
    out = eye(len(a))
    for _ in range(n):
        out = mul(out, a)
    return out


def determinant(a):
    a = [[Fraction(x) for x in row] for row in a]
    n = len(a)
    det = Fraction(1)
    for col in range(n):
        pivot = next((r for r in range(col, n) if a[r][col] != 0), None)
        if pivot is None:
            return 0
        if pivot != col:
            a[col], a[pivot] = a[pivot], a[col]
            det = -det
        p = a[col][col]
        det *= p
        for j in range(col, n):
            a[col][j] /= p
        for r in range(col + 1, n):
            q = a[r][col]
            if q:
                for j in range(col, n):
                    a[r][j] -= q * a[col][j]
    assert det.denominator == 1
    return det.numerator


def scalar_block(specs, sign=False):
    out = zeros(3)
    for coarse_perm, locals_ in specs:
        for source in range(3):
            target = PERM[coarse_perm][source]
            weight = SIGN[locals_[source]] if sign else 1
            out[source][target] += weight
    return out


def standard_block(specs):
    out = zeros(6)
    for coarse_perm, locals_ in specs:
        for source in range(3):
            target = PERM[coarse_perm][source]
            local = STD[locals_[source]]
            for i in range(2):
                for j in range(2):
                    out[2 * source + i][2 * target + j] += local[i][j]
    return out


TRIV_T3 = scalar_block(T3_SPECS)
TRIV_T5 = scalar_block(T5_SPECS)
SIGN_T3 = scalar_block(T3_SPECS, sign=True)
SIGN_T5 = scalar_block(T5_SPECS, sign=True)
STD_T3 = standard_block(T3_SPECS)
STD_T5 = standard_block(T5_SPECS)

TRIV_F = [[1, 0, 0], [0, 0, 1], [0, 1, 0]]
SIGN_F = [[-1, 0, 0], [0, 0, 1], [0, 1, 0]]
STD_F = [
    [-1, -1, 0, 0, 0, 0],
    [0, 1, 0, 0, 0, 0],
    [0, 0, 0, 0, 1, 0],
    [0, 0, 0, 0, 0, 1],
    [0, 0, 1, 0, 0, 0],
    [0, 0, 0, 1, 0, 0],
]

assert TRIV_T3 == [[2, 1, 1], [1, 0, 3], [1, 3, 0]]
assert TRIV_T5 == [[2, 2, 2], [2, 1, 3], [2, 3, 1]]
assert SIGN_T3 == [[-2, -1, 1], [-1, 0, -1], [1, -1, 0]]
assert SIGN_T5 == [[2, 0, 0], [0, -1, -3], [0, -3, -1]]
assert STD_T3 == [
    [-2, -2, 0, 1, -1, -1],
    [0, 2, 1, 0, 1, 0],
    [0, 1, 0, 0, 2, 1],
    [1, 0, 0, 0, 0, 0],
    [0, 1, 2, 1, 0, 0],
    [-1, -1, 0, 0, 0, 0],
]
assert STD_T5 == [
    [-1, 0, 2, 0, -1, 0],
    [0, -1, -1, 0, -1, 0],
    [2, 0, 1, 0, -2, -1],
    [-1, 0, -1, -1, 1, 2],
    [-2, -2, -2, -1, 1, 0],
    [1, 1, 1, 2, -1, -1],
]

# Every isotypic block carries the same commuting T3/T5/F family.
for t3, t5, frob in (
    (TRIV_T3, TRIV_T5, TRIV_F),
    (SIGN_T3, SIGN_T5, SIGN_F),
    (STD_T3, STD_T5, STD_F),
):
    assert mul(t3, t5) == mul(t5, t3)
    assert mul(t3, frob) == mul(frob, t3)
    assert mul(t5, frob) == mul(frob, t5)

# p(A)=(A-I)(A+3I)(A^2-3A-I)(A^2+A-I).
A = STD_T3
I6 = eye(6)
A2 = power(A, 2)
f1 = add(A, scale(-1, I6))
f2 = add(A, scale(3, I6))
f3 = add(add(A2, scale(-3, A)), scale(-1, I6))
f4 = add(add(A2, A), scale(-1, I6))
annihilator = mul(mul(mul(f1, f2), f3), f4)
assert annihilator == zeros(6)

# A cyclic vector proves the degree-six annihilator is minimal, hence is also
# the characteristic polynomial of the six-dimensional multiplicity block.
e = [0, 1, 0, 0, 0, 0]
columns = []
v = e
for _ in range(6):
    columns.append(v)
    v = matvec(A, v)
krylov = [[columns[j][i] for j in range(6)] for i in range(6)]
assert determinant(krylov) == -408

# Exact denominator-cleared polynomial relations.
A3 = power(A, 3)
A4 = power(A, 4)
A5 = power(A, 5)
rhs_t5 = scale(-38, I6)
for coeff, term in [(-242, A), (147, A2), (158, A3), (-12, A4), (-13, A5)]:
    rhs_t5 = add(rhs_t5, scale(coeff, term))
assert scale(34, STD_T5) == rhs_t5

rhs_f = scale(-7, I6)
for coeff, term in [(-126, A), (66, A2), (115, A3), (-4, A4), (-10, A5)]:
    rhs_f = add(rhs_f, scale(coeff, term))
assert scale(34, STD_F) == rhs_f

print("p37 deck-isotypic blocks verified")
print("dimensions: trivial=3 sign=3 standard-isotypic=12")
print("std multiplicity charpoly: (x-1)(x+3)(x^2-3x-1)(x^2+x-1)")
print("Krylov determinant:", determinant(krylov))
