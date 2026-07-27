#!/usr/bin/env python3
"""Verify the exact global-helicity obstruction on the known six-mode state."""

from __future__ import annotations

from fractions import Fraction

Complex = tuple[Fraction, Fraction]
Vector = list[Complex]
Mode = tuple[int, int, int]


def c(real: int | Fraction = 0, imag: int | Fraction = 0) -> Complex:
    return Fraction(real), Fraction(imag)


def add(a: Complex, b: Complex) -> Complex:
    return a[0] + b[0], a[1] + b[1]


def multiply(a: Complex, b: Complex) -> Complex:
    return a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0]


def conjugate(a: Complex) -> Complex:
    return a[0], -a[1]


def hermitian(v: Vector, w: Vector) -> Complex:
    total = c()
    for left, right in zip(v, w, strict=True):
        total = add(total, multiply(conjugate(left), right))
    return total


def curl_symbol(mode: Mode, value: Vector) -> Vector:
    x, y, z = mode
    a, b, d = value
    cross = [
        (y * d[0] - z * b[0], y * d[1] - z * b[1]),
        (z * a[0] - x * d[0], z * a[1] - x * d[1]),
        (x * b[0] - y * a[0], x * b[1] - y * a[1]),
    ]
    return [(-entry[1], entry[0]) for entry in cross]


def negate_mode(mode: Mode) -> Mode:
    return tuple(-coordinate for coordinate in mode)  # type: ignore[return-value]


def main() -> int:
    p = (-1, 0, 3)
    q = (2, -3, -3)
    k = (1, -3, 0)
    velocity: dict[Mode, Vector] = {
        p: [c(3, 3), c(-3, -3), c(1, 1)],
        q: [c(-3), c(), c(-2)],
        k: [c(3, -3), c(1, -1), c()],
    }
    for mode, value in list(velocity.items()):
        velocity[negate_mode(mode)] = [conjugate(entry) for entry in value]

    helicity_density = {
        mode: hermitian(value, curl_symbol(mode, value))[0]
        for mode, value in velocity.items()
    }
    assert all(value == 0 for value in helicity_density.values())

    helicity_dissipation = sum(
        sum(coordinate * coordinate for coordinate in mode) * density
        for mode, density in helicity_density.items()
    )
    assert helicity_dissipation == 0

    base_a = Fraction(8_503_484)
    b = Fraction(245_944)
    c_magnitude = Fraction(6_111_504)
    expected_gap = Fraction(28_984_957_666_432)

    for sign in (-1, 1):
        for epsilon in range(8):
            perturbed_a = base_a + sign * epsilon * helicity_dissipation
            gap = c_magnitude * c_magnitude - 4 * perturbed_a * b
            assert perturbed_a == base_a
            assert gap == expected_gap
            assert gap > 0

    print(
        "verified exact global-helicity obstruction: every mode has zero "
        "helicity density, helicity-dissipation correction=0, and "
        f"C^2-4AB={expected_gap} for both signs and every 0<=epsilon<8"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
