#!/usr/bin/env python3
"""Rigorously certified complex phase of 99^k with exact integer arithmetic.

Independent of Machin/floor certificates, same actual consumer:
    Im((cos 1 + i sin 1) ** (99**k)) = sin(99**k).
Classic de Moivre and Taylor alternating remainders; reuse and strengthen
scripts/check_pickover_fast_sine_complex_power.py (original proof owner).
The previous script's accuracy grid ended at 500 digits; here precision is
selected to match the magnitude of 99**k, not capped at a fixed grid.

Error in integer-scale Euclidean norm: e for |z/S - true_unit| <= e/S.
For rounded complex multiplication (per-coordinate rounding error <=1/(2S)):
  e_out <= e_a+e_b+e_a e_b/S+sqrt(2)/(2S)
and we conservatively use ceil(e_a e_b/S)+2 integer error units.
Norm-one property is true ONLY for actual exp(i)^N and its powers, not
for arbitrary input matrices. No analytic-j or CRT-only sign inference.
"""
from fractions import Fraction
from math import factorial


def ceiling_ratio(a, b):
    assert a >= 0 and b > 0
    return (a + b - 1) // b


def rounded_scaled(q, scale):
    return (2 * q.numerator * scale + q.denominator) // (2 * q.denominator)


def certified_seed(scale, terms):
    assert terms >= 2
    co = sum(((-1)**j * Fraction(1, factorial(2*j)) for j in range(terms)), Fraction())
    si = sum(((-1)**j * Fraction(1, factorial(2*j+1)) for j in range(terms)), Fraction())
    approx = (rounded_scaled(co, scale), rounded_scaled(si, scale))
    # |Taylor remainder| <= next term in each coordinate, |round| <= .5/scale.
    # L1 bounds Euclidean norm, so next Taylor terms + two rounded units suffice.
    error = (ceiling_ratio(scale, factorial(2*terms)) +
             ceiling_ratio(scale, factorial(2*terms+1)) + 2)
    return approx, error


def multiply(a, b, scale):
    x,y = a;u,v = b
    return ((x*u-y*v+scale//2)//scale,
            (x*v+y*u+scale//2)//scale)


def certify(base, exponent, digits):
    assert base >= 1 and exponent >= 0 and digits >= 10
    scale = 10**digits
    seed, err = certified_seed(scale, digits//2 + 5)
    actual_exponent = pow(base, exponent)
    out, out_err = (scale, 0), 0
    operations = 0
    while actual_exponent:
        if actual_exponent & 1:
            out = multiply(out, seed, scale)
            out_err = out_err + err + ceiling_ratio(out_err*err,scale)+2
            operations += 1
            if out_err >= scale:
                return None, operations, out_err, out
        actual_exponent >>= 1
        if actual_exponent:
            seed = multiply(seed, seed, scale)
            err = 2*err + ceiling_ratio(err*err,scale)+2
            operations += 1
            if err >= scale:
                return None, operations, err, out
    im = out[1]
    sign = 1 if im > out_err else (-1 if im < -out_err else None)
    return sign, operations, out_err, out


def run():
    expected = {1:-1, 2:-1, 6:1, 24:1, 120:-1, 720:1}
    for exponent, expected_sign in expected.items():
        # 99^k has <2*k digits, so choose a slightly larger decimal scale
        # to enclose exp(i * 99^k). Precision is not a constant 500.
        digits = 2*exponent+25
        sign, operations, err, result = certify(99, exponent, digits)
        assert sign == expected_sign, (exponent, sign, err)
        assert abs(result[1]) > err
        print(f'k={exponent} digits={digits} sign={sign:+d} complex_muls={operations}')
    assert pow(99,120,9999) == pow(99,720,9999) == 297
    print('PASS six exact rational/integer propagated-phase certificates')
    print('PASS same mod9999 residue, opposite actual signs for k=5!,6!')
    print('OPEN k=9999!; bitcount of 99^(9999!) and required digits are colossal')


if __name__ == '__main__':
    run()
