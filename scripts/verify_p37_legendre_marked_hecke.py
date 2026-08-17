#!/usr/bin/env python3
"""Verify the p=37 full-level-2 marked T3/T5 tables used by DASHI.

Pure Python, no third-party dependencies.

Sources:
- Adel Betina, Emmanuel Lecouturier,
  "Congruence formulae for Legendre modular polynomials",
  J. Number Theory 188 (2018), 71-87,
  DOI 10.1016/j.jnt.2018.01.006.
- Josep Gonzalez, "On the p-th division polynomial",
  J. Number Theory 233 (2022), 285-300,
  DOI 10.1016/j.jnt.2021.06.011.

The H_37 quadratic factorization is mirrored in
P37NonOggFullLevel2DeuringControlExact.agda.
"""

P = 37
D = 2  # a nonsquare mod 37; u^2 = 2 gives F_37^2


def add(x, y):
    return ((x[0] + y[0]) % P, (x[1] + y[1]) % P)


def neg(x):
    return ((-x[0]) % P, (-x[1]) % P)


def sub(x, y):
    return add(x, neg(y))


def mul(x, y):
    a, b = x
    c, e = y
    return ((a*c + D*b*e) % P, (a*e + b*c) % P)


def fpow(x, n):
    r = (1, 0)
    while n:
        if n & 1:
            r = mul(r, x)
        x = mul(x, x)
        n //= 2
    return r


def inv(x):
    a, b = x
    den = (a*a - D*b*b) % P
    if den == 0:
        raise ZeroDivisionError(x)
    di = pow(den, -1, P)
    return (a*di % P, -b*di % P)


def div(x, y):
    return mul(x, inv(y))


def scalar(n):
    return (n % P, 0)


def smul(n, x):
    return mul(scalar(n), x)


def sumf(*xs):
    r = (0, 0)
    for x in xs:
        r = add(r, x)
    return r


# H_37 factors x^2 + b x + c, coefficients mod 37.
FACTORS = [
    (2, 9), (4, 33), (6, 26), (12, 34), (23, 10),
    (29, 33), (31, 1), (33, 12), (36, 9),
]

INV2 = pow(2, -1, P)
U = (0, 1)


def roots_of_factor(q, b, c):
    delta = (b*b - 4*c) % P
    ratio = delta * pow(D, -1, P) % P
    s = next(t for t in range(P) if t*t % P == ratio)
    sqrt_delta = mul(scalar(s), U)
    r0 = mul(scalar(INV2), add(scalar(-b), sqrt_delta))
    r1 = mul(scalar(INV2), sub(scalar(-b), sqrt_delta))
    return [(q, 0, r0), (q, 1, r1)]


ROOTS = []
for q, (b, c) in enumerate(FACTORS):
    ROOTS.extend(roots_of_factor(q, b, c))

assert len(ROOTS) == 18
for q, bit, x in ROOTS:
    b, c = FACTORS[q]
    assert sumf(mul(x, x), mul(scalar(b), x), scalar(c)) == (0, 0)
    assert fpow(x, P) == (x[0], (-x[1]) % P)
    mate = ROOTS[2*q + (1-bit)][2]
    assert fpow(x, P) == mate

# Monomial tables (coefficient, X exponent, Y exponent) for the published
# Legendre modular polynomials F_3 and F_5.
F3_TERMS = [
    (1,4,0), (1,0,4),
    (-256,3,3), (384,3,2), (-132,3,1),
    (384,2,3), (-762,2,2), (384,2,1),
    (-132,1,3), (384,1,2), (-256,1,1),
]

F5_TERMS = [
    (1,6,0), (1,0,6),
    (-65536,5,5),
    (163840,5,4), (163840,4,5),
    (-138240,5,3), (-133120,4,4), (-138240,3,5),
    (43520,5,2), (-207360,4,3), (-207360,3,4), (43520,2,5),
    (-3590,5,1), (133135,4,2), (691180,3,3),
    (133135,2,4), (-3590,1,5),
    (43520,4,1), (-207360,3,2), (-207360,2,3), (43520,1,4),
    (-138240,3,1), (-133120,2,2), (-138240,1,3),
    (163840,2,1), (163840,1,2),
    (-65536,1,1),
]


def eval_terms(terms, x, y, dy=0):
    r = (0, 0)
    for coeff, xp, yp in terms:
        if yp < dy:
            continue
        falling = 1
        for t in range(dy):
            falling *= yp - t
        r = add(r, smul(coeff * falling, mul(fpow(x, xp), fpow(y, yp-dy))))
    return r


def root_multiplicity(terms, x, y):
    if eval_terms(terms, x, y) != (0, 0):
        return 0
    for order in range(1, 8):
        if eval_terms(terms, x, y, dy=order) != (0, 0):
            return order
    raise AssertionError("unexpected multiplicity")


def adjacency(terms):
    result = []
    for _, _, x in ROOTS:
        row = []
        for j, (_, _, y) in enumerate(ROOTS):
            m = root_multiplicity(terms, x, y)
            row.extend([j] * m)
        result.append(row)
    return result


T3 = adjacency(F3_TERMS)
T5 = adjacency(F5_TERMS)
assert all(len(row) == 4 for row in T3)
assert all(len(row) == 6 for row in T5)

# j(lambda) = 256 (1-lambda+lambda^2)^3 / (lambda^2 (1-lambda)^2)
def j_invariant(lam):
    one = (1, 0)
    numerator = smul(256, fpow(add(sub(one, lam), mul(lam, lam)), 3))
    denominator = mul(mul(lam, lam), fpow(sub(one, lam), 2))
    return div(numerator, denominator)


J = [j_invariant(x) for _, _, x in ROOTS]
J8 = (8, 0)
JA = (3, 10)
JB = (3, 27)
assert set(J) == {J8, JA, JB}
CLASS = [{J8:0, JA:1, JB:2}[j] for j in J]
assert [CLASS.count(i) for i in range(3)] == [6, 6, 6]


def aggregate(row):
    out = [0, 0, 0]
    for j in row:
        out[CLASS[j]] += 1
    return tuple(out)


EXPECTED_T3 = ((2,1,1), (1,0,3), (1,3,0))
EXPECTED_T5 = ((2,2,2), (2,1,3), (2,3,1))
for i in range(18):
    assert aggregate(T3[i]) == EXPECTED_T3[CLASS[i]]
    assert aggregate(T5[i]) == EXPECTED_T5[CLASS[i]]

# Frobenius equivariance: source/target conjugation preserves multiplicity.
FROB = [i ^ 1 for i in range(18)]
for table in (T3, T5):
    for i, row in enumerate(table):
        lhs = sorted(FROB[j] for j in row)
        rhs = sorted(table[FROB[i]])
        assert lhs == rhs

# Anharmonic/deck S3 on lambda: r(lambda)=1/(1-lambda), s(lambda)=1-lambda.
ROOT_INDEX = {x:i for i, (_,_,x) in enumerate(ROOTS)}
ONE = (1,0)


def deck_r_value(lam):
    return inv(sub(ONE, lam))


def deck_s_value(lam):
    return sub(ONE, lam)


DECK_R = [ROOT_INDEX[deck_r_value(x)] for _,_,x in ROOTS]
DECK_S = [ROOT_INDEX[deck_s_value(x)] for _,_,x in ROOTS]


def compose_perm(p, q):
    return [p[q[i]] for i in range(len(p))]


ID18 = list(range(18))
assert compose_perm(DECK_R, compose_perm(DECK_R, DECK_R)) == ID18
assert compose_perm(DECK_S, DECK_S) == ID18
assert compose_perm(DECK_S, compose_perm(DECK_R, DECK_S)) == compose_perm(DECK_R, DECK_R)
assert all(CLASS[DECK_R[i]] == CLASS[i] for i in range(18))
assert all(CLASS[DECK_S[i]] == CLASS[i] for i in range(18))

for table in (T3, T5):
    for deck in (DECK_R, DECK_S):
        for i, row in enumerate(table):
            assert sorted(deck[j] for j in row) == sorted(table[deck[i]])

# Regular-S3 coordinates: coarse class x side x C3 phase.
CYCLES = {
    0: {0:[2,12,17], 1:[13,16,3]},
    1: {0:[0,7,5],   1:[15,10,8]},
    2: {0:[1,6,4],   1:[14,11,9]},
}
COORD = {}
FROM_COORD = {}
for c in range(3):
    for side in range(2):
        for phase, i in enumerate(CYCLES[c][side]):
            COORD[i] = (c, side, phase)
            FROM_COORD[(c, side, phase)] = i
assert len(COORD) == 18
assert [FROM_COORD[(c,s,(ph+1)%3)] for c,s,ph in map(COORD.get, range(18))] == DECK_R
assert [FROM_COORD[(c,1-s,(-ph)%3)] for c,s,ph in map(COORD.get, range(18))] == DECK_S

# Six left translations commuting with the right deck S3 action, in local
# coordinate order (side0 phases 0,1,2, side1 phases 0,1,2).
LEFT6 = [
    (0,1,2,3,4,5),
    (1,2,0,5,3,4),
    (2,0,1,4,5,3),
    (3,4,5,0,1,2),
    (4,5,3,2,0,1),
    (5,3,4,1,2,0),
]


def local_index(side, phase):
    return side*3 + phase


def global_orbital(coarse_sigma, left_choices):
    out = [None]*18
    for i in range(18):
        c, side, phase = COORD[i]
        local = LEFT6[left_choices[c]][local_index(side, phase)]
        side2, phase2 = divmod(local, 3)
        out[i] = FROM_COORD[(coarse_sigma[c], side2, phase2)]
    assert len(set(out)) == 18
    assert compose_perm(out, DECK_R) == compose_perm(DECK_R, out)
    assert compose_perm(out, DECK_S) == compose_perm(DECK_S, out)
    return out

# One exact deck-equivariant permutation decomposition for each marked Hecke
# correspondence.  (coarse permutation, left-translation choices on c0,c1,c2)
T3_ORBITAL_SPECS = [
    ((0,2,1), (5,0,0)),
    ((0,2,1), (5,3,3)),
    ((1,2,0), (3,4,1)),
    ((2,0,1), (2,3,4)),
]
T5_ORBITAL_SPECS = [
    ((0,2,1), (1,3,5)),
    ((0,2,1), (2,5,3)),
    ((1,0,2), (0,0,4)),
    ((1,2,0), (4,5,2)),
    ((2,0,1), (1,4,5)),
    ((2,1,0), (5,4,5)),
]


def table_count(table):
    counts = [[0]*18 for _ in range(18)]
    for i,row in enumerate(table):
        for j in row:
            counts[i][j] += 1
    return counts


def orbital_sum(specs):
    counts = [[0]*18 for _ in range(18)]
    perms = []
    for sigma, choices in specs:
        perm = global_orbital(sigma, choices)
        perms.append(perm)
        for i,j in enumerate(perm):
            counts[i][j] += 1
    return counts, perms


T3_ORBITAL_COUNTS, T3_PERMS = orbital_sum(T3_ORBITAL_SPECS)
T5_ORBITAL_COUNTS, T5_PERMS = orbital_sum(T5_ORBITAL_SPECS)
assert T3_ORBITAL_COUNTS == table_count(T3)
assert T5_ORBITAL_COUNTS == table_count(T5)

# Frobenius need only preserve the SUM; it may permute individual isogeny
# summands.  Verify the exact aggregate statement again after decomposition.
for counts in (T3_ORBITAL_COUNTS, T5_ORBITAL_COUNTS):
    for i in range(18):
        for j in range(18):
            assert counts[FROB[i]][FROB[j]] == counts[i][j]


def state_name(i):
    q, bit, _ = ROOTS[i]
    return f"q{q}r{bit}"


print("p=37 marked Legendre verification: OK")
print("18 Deuring roots; T3 degree 4; T5 degree 6")
print("coarse T3 =", EXPECTED_T3)
print("coarse T5 =", EXPECTED_T5)
print("j-fibres =", {
    0: [state_name(i) for i,c in enumerate(CLASS) if c == 0],
    1: [state_name(i) for i,c in enumerate(CLASS) if c == 1],
    2: [state_name(i) for i,c in enumerate(CLASS) if c == 2],
})
