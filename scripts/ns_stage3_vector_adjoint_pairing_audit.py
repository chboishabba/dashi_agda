#!/usr/bin/env python3
"""Exact rational audit of Leray self-adjointness and literal vector adjoints."""

from __future__ import annotations

from fractions import Fraction
import random

Gaussian = tuple[Fraction, Fraction]
Vector = tuple[Gaussian, Gaussian, Gaussian]
Mode = tuple[int, int, int]

ZERO: Gaussian = (Fraction(0), Fraction(0))
I: Gaussian = (Fraction(0), Fraction(1))
MINUS_I: Gaussian = (Fraction(0), Fraction(-1))


def add(a: Gaussian, b: Gaussian) -> Gaussian:
    return a[0] + b[0], a[1] + b[1]


def neg(a: Gaussian) -> Gaussian:
    return -a[0], -a[1]


def mul(a: Gaussian, b: Gaussian) -> Gaussian:
    return a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0]


def conj(a: Gaussian) -> Gaussian:
    return a[0], -a[1]


def vadd(a: Vector, b: Vector) -> Vector:
    return tuple(add(x, y) for x, y in zip(a, b))  # type: ignore[return-value]


def vneg(a: Vector) -> Vector:
    return tuple(neg(x) for x in a)  # type: ignore[return-value]


def vsub(a: Vector, b: Vector) -> Vector:
    return vadd(a, vneg(b))


def scale(s: Gaussian, a: Vector) -> Vector:
    return tuple(mul(s, x) for x in a)  # type: ignore[return-value]


def mode_vector(k: Mode) -> Vector:
    return tuple((Fraction(x), Fraction(0)) for x in k)  # type: ignore[return-value]


def dot(a: Vector, b: Vector) -> Gaussian:
    total = ZERO
    for x, y in zip(a, b):
        total = add(total, mul(x, y))
    return total


def hermitian(a: Vector, b: Vector) -> Gaussian:
    return dot(tuple(conj(x) for x in a), b)  # type: ignore[arg-type]


def mode_add(a: Mode, b: Mode) -> Mode:
    return a[0] + b[0], a[1] + b[1], a[2] + b[2]


def cross_mode(k: Mode, a: Vector) -> Vector:
    m = mode_vector(k)
    return (
        add(mul(m[1], a[2]), neg(mul(m[2], a[1]))),
        add(mul(m[2], a[0]), neg(mul(m[0], a[2]))),
        add(mul(m[0], a[1]), neg(mul(m[1], a[0]))),
    )


def norm_squared_mode(k: Mode) -> int:
    return k[0] * k[0] + k[1] * k[1] + k[2] * k[2]


def leray(k: Mode, a: Vector) -> Vector:
    norm = norm_squared_mode(k)
    if norm == 0:
        raise ValueError("zero Leray mode")
    coefficient = mul((Fraction(1, norm), Fraction(0)), dot(mode_vector(k), a))
    return vsub(a, scale(coefficient, mode_vector(k)))


def ordered_interaction(k: Mode, p: Mode, q: Mode, u_p: Vector, u_q: Vector) -> Vector:
    del p
    inner = scale(dot(u_p, mode_vector(q)), u_q)
    return scale(MINUS_I, leray(k, inner))


def output_value(k: Mode, p: Mode, q: Mode, u_p: Vector, u_q: Vector, test_k: Vector) -> Fraction:
    return hermitian(test_k, ordered_interaction(k, p, q, u_p, u_q))[0]


def direct_first_candidate(p: Mode, q: Mode, test_k: Vector, u_q: Vector) -> Vector:
    scalar = mul(I, hermitian(u_q, test_k))
    return leray(p, scale(scalar, mode_vector(q)))


def second_candidate(q: Mode, u_p: Vector, test_k: Vector) -> Vector:
    scalar = conj(mul(MINUS_I, dot(u_p, mode_vector(q))))
    return leray(q, scale(scalar, test_k))


def swapped_first_candidate(p: Mode, test_k: Vector, u_q: Vector) -> Vector:
    scalar = conj(mul(MINUS_I, dot(u_q, mode_vector(p))))
    return leray(p, scale(scalar, test_k))


def random_gaussian(rng: random.Random) -> Gaussian:
    return (
        Fraction(rng.randint(-4, 4), rng.randint(1, 5)),
        Fraction(rng.randint(-4, 4), rng.randint(1, 5)),
    )


def random_vector(rng: random.Random) -> Vector:
    return random_gaussian(rng), random_gaussian(rng), random_gaussian(rng)


def random_nonzero_mode(rng: random.Random) -> Mode:
    while True:
        mode = rng.randint(-5, 5), rng.randint(-5, 5), rng.randint(-5, 5)
        if mode != (0, 0, 0):
            return mode


def verify_case(rng: random.Random) -> None:
    while True:
        p = random_nonzero_mode(rng)
        q = random_nonzero_mode(rng)
        k = mode_add(p, q)
        if k != (0, 0, 0):
            break

    u_p = cross_mode(p, random_vector(rng))
    u_q = cross_mode(q, random_vector(rng))
    test_k = cross_mode(k, random_vector(rng))

    assert dot(mode_vector(p), u_p) == ZERO
    assert dot(mode_vector(q), u_q) == ZERO
    assert dot(mode_vector(k), test_k) == ZERO

    arbitrary_u = random_vector(rng)
    arbitrary_v = random_vector(rng)
    assert hermitian(leray(p, arbitrary_u), arbitrary_v) == hermitian(
        arbitrary_u, leray(p, arbitrary_v)
    )

    direct_pair = hermitian(u_p, direct_first_candidate(p, q, test_k, u_q))[0]
    second_pair = hermitian(u_q, second_candidate(q, u_p, test_k))[0]
    output = output_value(k, p, q, u_p, u_q, test_k)
    assert direct_pair == output
    assert second_pair == output

    swapped_pair = hermitian(u_p, swapped_first_candidate(p, test_k, u_q))[0]
    swapped_output = output_value(k, q, p, u_q, u_p, test_k)
    assert swapped_pair == swapped_output

    ordered_candidate = vadd(
        direct_first_candidate(p, q, test_k, u_q),
        swapped_first_candidate(p, test_k, u_q),
    )
    ordered_pair = hermitian(u_p, ordered_candidate)[0]
    assert ordered_pair == output + swapped_output


def main() -> int:
    rng = random.Random(20260727)
    case_count = 2_000
    for _ in range(case_count):
        verify_case(rng)
    print(
        f"verified {case_count} exact rational cases of Leray self-adjointness, "
        "direct T*1, T*2, swapped T*1, and full ordered-pair T*1 pairing identities"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
