#!/usr/bin/env python3
"""Independent finite verifier for the p=43 full-level-2 Deuring control.

Pure Python, no Sage/SymPy dependency.  It checks:
  * H_43 coefficients from binomial squares;
  * the displayed 3-linear + 9-quadratic factorization;
  * irreducibility of all nine quadratic factors over F_43;
  * Legendre j on the three rational roots is 8=1728 mod43;
  * three quadratic factors have constant j=41;
  * the remaining six push forward to J^2+19J+16;
  * that coarse quadratic has nonsquare discriminant 39.
"""

from math import comb

P = 43


def trim(a):
    while len(a) > 1 and a[-1] % P == 0:
        a.pop()
    return [x % P for x in a]


def add(a, b):
    n = max(len(a), len(b))
    return trim([(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(n)])


def mul(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] = (out[i + j] + x * y) % P
    return trim(out)


H = [comb(21, k) ** 2 % P for k in range(22)]
expected_H = [1,11,25,9,21,14,4,21,24,23,40,40,23,24,21,4,14,21,9,25,11,1]
assert H == expected_H

# Factors are low coefficient first.
linear_roots = [2, 42, 22]  # 2, -1, -21
linear_factors = [[(-r) % P, 1] for r in linear_roots]
quadratics = [
    (1, 36),   # x^2+x-7
    (6, 6),
    (6, 10),
    (9, 1),
    (32, 11),  # x^2-11x+11
    (35, 13),
    (35, 17),
    (40, 38),
    (42, 4),
]
quad_factors = [[c, b, 1] for b, c in quadratics]
product = [1]
for f in linear_factors + quad_factors:
    product = mul(product, f)
assert product == H

squares = {x * x % P for x in range(P)}
discriminants = [(b*b - 4*c) % P for b,c in quadratics]
assert discriminants == [29,12,39,34,34,12,39,29,28]
assert all(d not in squares for d in discriminants)
assert 39 not in squares

# Quadratic quotient arithmetic: alpha^2 = -b alpha - c.
def qmul(x, y, b, c):
    a0, a1 = x
    d0, d1 = y
    return ((a0*d0 - c*a1*d1) % P,
            (a0*d1 + a1*d0 - b*a1*d1) % P)


def qadd(x, y):
    return ((x[0] + y[0]) % P, (x[1] + y[1]) % P)


def qpow(x, n, b, c):
    out = (1,0)
    while n:
        if n & 1:
            out = qmul(out, x, b, c)
        x = qmul(x, x, b, c)
        n >>= 1
    return out


def qinv(x, b, c):
    assert x != (0,0)
    # finite-field inverse in F_(43^2)
    return qpow(x, P*P - 2, b, c)


def j_of_alpha(b, c):
    a = (0,1)
    one = (1,0)
    a2 = qmul(a,a,b,c)
    one_minus_a = qadd(one, ((-a[0])%P, (-a[1])%P))
    one_minus_a_plus_a2 = qadd(one_minus_a, a2)
    numerator = qpow(one_minus_a_plus_a2, 3, b, c)
    numerator = ((256 * numerator[0]) % P, (256 * numerator[1]) % P)
    denominator = qmul(a2, qpow(one_minus_a, 2, b, c), b, c)
    return qmul(numerator, qinv(denominator,b,c), b, c)


def j_rational(lam):
    num = 256 * pow((1-lam+lam*lam) % P, 3, P)
    den = (lam*lam * (1-lam)*(1-lam)) % P
    return num * pow(den, P-2, P) % P

assert [j_rational(r) for r in linear_roots] == [8,8,8]

j_values = [j_of_alpha(b,c) for b,c in quadratics]
# q3,q4,q8 are exactly the constant-j=41 factors.
for idx in (3,4,8):
    assert j_values[idx] == (41,0)

# The remaining six j-values satisfy J^2+19J+16=0 in their own quotient.
for idx, ((b,c), j) in enumerate(zip(quadratics, j_values)):
    if idx in (3,4,8):
        continue
    lhs = qadd(qadd(qmul(j,j,b,c), ((19*j[0])%P,(19*j[1])%P)), (16,0))
    assert lhs == (0,0)

assert (19*19 - 4*16) % P == 39

print("p43 Deuring/full-level2 control verified")
print("marked: 3 fixed + 9 Frobenius pairs = 21")
print("coarse: j=8 fixed, j=41 fixed, one quadratic pair")
print("coarse quadratic: J^2 + 19J + 16, discriminant 39 nonsquare")
