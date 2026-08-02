#!/usr/bin/env python3
"""Exact Stage-3 Hermitian, Leray, and low-output convolution audit."""

from __future__ import annotations

from fractions import Fraction
from itertools import product
import random

Gaussian = tuple[Fraction, Fraction]
Vector = tuple[Gaussian, Gaussian, Gaussian]
Mode = tuple[int, int, int]

ZERO: Gaussian = (Fraction(0), Fraction(0))
ONE: Gaussian = (Fraction(1), Fraction(0))
IMAGINARY: Gaussian = (Fraction(0), Fraction(1))


def gadd(left: Gaussian, right: Gaussian) -> Gaussian:
    return left[0] + right[0], left[1] + right[1]


def gneg(value: Gaussian) -> Gaussian:
    return -value[0], -value[1]


def gmul(left: Gaussian, right: Gaussian) -> Gaussian:
    return (
        left[0] * right[0] - left[1] * right[1],
        left[0] * right[1] + left[1] * right[0],
    )


def gconj(value: Gaussian) -> Gaussian:
    return value[0], -value[1]


def gnorm_squared(value: Gaussian) -> Fraction:
    return value[0] * value[0] + value[1] * value[1]


def gsum(values: list[Gaussian] | tuple[Gaussian, ...]) -> Gaussian:
    total = ZERO
    for value in values:
        total = gadd(total, value)
    return total


def vscale(scalar: Gaussian, value: Vector) -> Vector:
    return tuple(gmul(scalar, coordinate) for coordinate in value)  # type: ignore[return-value]


def vconj(value: Vector) -> Vector:
    return tuple(gconj(coordinate) for coordinate in value)  # type: ignore[return-value]


def bilinear_dot(left: Vector, right: Vector) -> Gaussian:
    return gsum([gmul(a, b) for a, b in zip(left, right)])


def hermitian_pairing(left: Vector, right: Vector) -> Gaussian:
    return bilinear_dot(vconj(left), right)


def mode_vector(mode: Mode) -> Vector:
    return tuple((Fraction(coordinate), Fraction(0)) for coordinate in mode)  # type: ignore[return-value]


def cross_mode_vector(mode: Mode, value: Vector) -> Vector:
    p = mode_vector(mode)
    return (
        gadd(gmul(p[1], value[2]), gneg(gmul(p[2], value[1]))),
        gadd(gmul(p[2], value[0]), gneg(gmul(p[0], value[2]))),
        gadd(gmul(p[0], value[1]), gneg(gmul(p[1], value[0]))),
    )


def leray_project(mode: Mode, value: Vector) -> Vector:
    norm_squared = sum(coordinate * coordinate for coordinate in mode)
    if norm_squared == 0:
        raise ValueError("Leray projection requires a nonzero mode")
    factor = gmul(
        (Fraction(1, norm_squared), Fraction(0)),
        bilinear_dot(mode_vector(mode), value),
    )
    return tuple(
        gadd(coordinate, gneg(gmul(factor, mode_coordinate)))
        for coordinate, mode_coordinate in zip(value, mode_vector(mode))
    )  # type: ignore[return-value]


def add_mode(left: Mode, right: Mode) -> Mode:
    return (
        left[0] + right[0],
        left[1] + right[1],
        left[2] + right[2],
    )


def dyadic_shell(index: int) -> list[Mode]:
    lower = 2**index
    upper = 2 ** (index + 1)
    return [
        (x, y, z)
        for x in range(-upper + 1, upper)
        for y in range(-upper + 1, upper)
        for z in range(-upper + 1, upper)
        if lower * lower <= x * x + y * y + z * z < upper * upper
    ]


def sequence_norm_squared(sequence: dict[Mode, Gaussian]) -> Fraction:
    return sum(
        (gnorm_squared(value) for value in sequence.values()),
        Fraction(0),
    )


def convolution_at(
    left: dict[Mode, Gaussian],
    right: dict[Mode, Gaussian],
    output: Mode,
) -> Gaussian:
    return gsum(
        [
            gmul(left.get(add_mode(output, source), ZERO), source_value)
            for source, source_value in right.items()
        ]
    )


def random_gaussian(rng: random.Random) -> Gaussian:
    return (
        Fraction(rng.randint(-3, 3), rng.randint(1, 4)),
        Fraction(rng.randint(-3, 3), rng.randint(1, 4)),
    )


def random_vector(rng: random.Random) -> Vector:
    return random_gaussian(rng), random_gaussian(rng), random_gaussian(rng)


def random_sequence(
    rng: random.Random,
    mode_pool: list[Mode],
    size: int,
) -> dict[Mode, Gaussian]:
    return {mode: random_gaussian(rng) for mode in rng.sample(mode_pool, size)}


def verify_complex_and_hermitian_laws(rng: random.Random) -> int:
    cases = 0
    for _ in range(1_000):
        a = random_gaussian(rng)
        b = random_gaussian(rng)
        c = random_gaussian(rng)
        u = random_vector(rng)
        v = random_vector(rng)
        scalar = random_gaussian(rng)

        assert gconj(gadd(a, b)) == gadd(gconj(a), gconj(b))
        assert gconj(gmul(a, b)) == gmul(gconj(a), gconj(b))
        assert gmul(gmul(a, b), c) == gmul(a, gmul(b, c))
        assert gconj(hermitian_pairing(u, v)) == hermitian_pairing(v, u)
        assert hermitian_pairing(vscale(scalar, u), v) == gmul(
            gconj(scalar), hermitian_pairing(u, v)
        )
        assert hermitian_pairing(u, vscale(scalar, v)) == gmul(
            scalar, hermitian_pairing(u, v)
        )

        basis = (
            ((ONE, ZERO, ZERO), (IMAGINARY, ZERO, ZERO)),
            ((ZERO, ONE, ZERO), (ZERO, IMAGINARY, ZERO)),
            ((ZERO, ZERO, ONE), (ZERO, ZERO, IMAGINARY)),
        )
        recovered: list[Gaussian] = []
        for real_probe, imaginary_probe in basis:
            real_value = hermitian_pairing(real_probe, u)[0]
            imaginary_value = hermitian_pairing(imaginary_probe, u)[0]
            recovered.append((real_value, imaginary_value))
        assert tuple(recovered) == u
        cases += 1
    return cases


def verify_leray_transverse_fixed_point(rng: random.Random) -> int:
    cases = 0
    for _ in range(512):
        mode = (
            rng.randint(-5, 5),
            rng.randint(-5, 5),
            rng.randint(-5, 5),
        )
        if mode == (0, 0, 0):
            continue
        value = cross_mode_vector(mode, random_vector(rng))
        assert bilinear_dot(mode_vector(mode), value) == ZERO
        assert leray_project(mode, value) == value
        cases += 1
    return cases


def verify_shell_cardinality() -> list[int]:
    counts: list[int] = []
    for index in range(5):
        count = len(dyadic_shell(index))
        assert count <= 125 * (8**index)
        counts.append(count)
    return counts


def verify_translation_injectivity() -> int:
    checks = 0
    modes = list(product(range(-4, 5), repeat=3))
    for output in ((0, 0, 0), (1, -2, 3), (-4, 1, 2)):
        images: dict[Mode, Mode] = {}
        for source in modes:
            image = add_mode(output, source)
            assert image not in images or images[image] == source
            images[image] = source
            checks += 1
    return checks


def verify_low_output_convolution(rng: random.Random) -> int:
    mode_pool = list(product(range(-3, 4), repeat=3))
    checks = 0
    for _ in range(128):
        left = random_sequence(rng, mode_pool, 18)
        right = random_sequence(rng, mode_pool, 17)
        left_norm = sequence_norm_squared(left)
        right_norm = sequence_norm_squared(right)
        pointwise_bound = left_norm * right_norm

        for shell_index in (0, 1):
            shell = dyadic_shell(shell_index)
            shell_total = Fraction(0)
            for output in shell:
                value = convolution_at(left, right, output)
                value_norm = gnorm_squared(value)
                assert value_norm <= pointwise_bound
                shell_total += value_norm
                checks += 1
            assert shell_total <= len(shell) * pointwise_bound
    return checks


def verify_endpoint_and_gap_arithmetic() -> None:
    twice_s = Fraction(5)
    low_decay_times_two = 2 * twice_s - 5
    gap_decay_times_two = 2 * twice_s - 2
    assert low_decay_times_two == 5
    assert gap_decay_times_two == 8
    assert 48 * 8 * 2 == 768

    low = (1, 0, 0)
    high = (0, 37, 0)
    output = add_mode(low, high)
    low_norm_squared = sum(x * x for x in low)
    high_norm_squared = sum(x * x for x in high)
    output_norm_squared = sum(x * x for x in output)
    assert (low_norm_squared, high_norm_squared, output_norm_squared) == (
        1,
        1369,
        1370,
    )
    assert 16 * low_norm_squared <= high_norm_squared
    assert 9 * high_norm_squared <= 16 * output_norm_squared
    assert 16 * output_norm_squared <= 25 * high_norm_squared


def main() -> int:
    rng = random.Random(20260727)

    hermitian_cases = verify_complex_and_hermitian_laws(rng)
    leray_cases = verify_leray_transverse_fixed_point(rng)
    shell_counts = verify_shell_cardinality()
    translation_checks = verify_translation_injectivity()
    convolution_checks = verify_low_output_convolution(rng)
    verify_endpoint_and_gap_arithmetic()

    print(
        "verified "
        f"{hermitian_cases} Hermitian/scale/six-probe cases, "
        f"{leray_cases} transverse Leray fixed points, "
        f"{translation_checks} translation injections, and "
        f"{convolution_checks} exact low-output convolution inequalities; "
        f"shell counts={shell_counts}, endpoint decay=(5/2,4), "
        "base transport factor=768"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
