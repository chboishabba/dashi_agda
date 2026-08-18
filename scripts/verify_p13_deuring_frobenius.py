#!/usr/bin/env python3
"""Independent finite-field check for the p=13 Deuring/Frobenius control.

This script uses only Python's standard library.  It verifies:

1. H_13(lambda) = sum_i binom(6,i)^2 lambda^i mod 13 has coefficients
   [1,10,4,10,4,10,1].
2. H_13 factors as
      (x^2+4x+9)(x^2+7x+1)(x^2+12x+3)
   modulo 13.
3. Each quadratic is irreducible over F_13.
4. The Legendre j-rational function
      256(1-x+x^2)^3 / (x^2(1-x)^2)
   reduces to the constant 5 in each quadratic quotient.

Hence the six marked level-2 supersingular lambda points are three Frobenius
pairs, while all six forget to the single rational coarse j-class j=5.
"""

from math import comb

P = 13


def trim(poly):
    out = [c % P for c in poly]
    while len(out) > 1 and out[-1] == 0:
        out.pop()
    return out


def add(a, b):
    n = max(len(a), len(b))
    return trim([
        (a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0)
        for i in range(n)
    ])


def scale(a, scalar):
    return trim([scalar * c for c in a])


def mul(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        for j, bj in enumerate(b):
            out[i + j] = (out[i + j] + ai * bj) % P
    return trim(out)


def divmod_poly(dividend, divisor):
    f = trim(dividend)
    g = trim(divisor)
    if g == [0]:
        raise ZeroDivisionError("zero polynomial")
    q = [0] * max(1, len(f) - len(g) + 1)
    inv_lead = pow(g[-1], -1, P)
    while len(f) >= len(g) and f != [0]:
        shift = len(f) - len(g)
        coeff = f[-1] * inv_lead % P
        q[shift] = coeff
        for i, gi in enumerate(g):
            f[shift + i] = (f[shift + i] - coeff * gi) % P
        f = trim(f)
    return trim(q), trim(f)


def mod_poly(poly, modulus):
    return divmod_poly(poly, modulus)[1]


def discriminant_of_monic_quadratic(poly):
    c, b, one = poly
    assert one == 1
    return (b * b - 4 * c) % P


def main():
    h13 = [comb(6, i) ** 2 % P for i in range(7)]
    expected = [1, 10, 4, 10, 4, 10, 1]
    assert h13 == expected, (h13, expected)

    factors = [
        [9, 4, 1],   # x^2 + 4x + 9
        [1, 7, 1],   # x^2 + 7x + 1
        [3, 12, 1],  # x^2 + 12x + 3
    ]

    product = [1]
    for factor in factors:
        product = mul(product, factor)
    assert product == h13, (product, h13)

    square_residues = {x * x % P for x in range(P)}
    discriminants = [discriminant_of_monic_quadratic(f) for f in factors]
    assert discriminants == [6, 6, 2], discriminants
    assert all(d not in square_residues for d in discriminants)

    x = [0, 1]
    one_minus_x_plus_x2 = [1, -1, 1]
    numerator = scale(
        mul(mul(one_minus_x_plus_x2, one_minus_x_plus_x2),
            one_minus_x_plus_x2),
        256,
    )
    denominator = mul(mul(x, x), mul([1, -1], [1, -1]))

    expected_num_remainders = [[8, 2], [10, 11], [6]]
    expected_den_remainders = [[12, 3], [2, 10], [9]]

    for i, factor in enumerate(factors):
        num_r = mod_poly(numerator, factor)
        den_r = mod_poly(denominator, factor)
        assert num_r == expected_num_remainders[i], (i, num_r)
        assert den_r == expected_den_remainders[i], (i, den_r)
        assert num_r == mod_poly(scale(den_r, 5), factor), (i, num_r, den_r)

    print("p=13 Deuring/Frobenius verification passed")
    print("H13 coefficients:", h13)
    print("irreducible quadratic discriminants:", discriminants)
    print("marked Frobenius: 0 fixed + 3 pairs = 6 lambda points")
    print("coarse Legendre j: all factors map to j=5 in F_13")
    print("coarse Frobenius: 1 fixed + 0 pairs")


if __name__ == "__main__":
    main()
