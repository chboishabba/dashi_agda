#!/usr/bin/env python3
"""Verify the exact six-mode H^3 zero-coherence discriminant failure."""

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


def scale(real: Fraction, a: Complex) -> Complex:
    return real * a[0], real * a[1]


def conjugate(a: Complex) -> Complex:
    return a[0], -a[1]


def minus_i(a: Complex) -> Complex:
    return a[1], -a[0]


def vector_add(a: Vector, b: Vector) -> Vector:
    return [add(x, y) for x, y in zip(a, b, strict=True)]


def vector_scale(z: Complex, v: Vector) -> Vector:
    return [multiply(z, x) for x in v]


def mode_dot(mode: Mode, v: Vector) -> Complex:
    total = c()
    for coordinate, value in zip(mode, v, strict=True):
        total = add(total, scale(Fraction(coordinate), value))
    return total


def hermitian(v: Vector, w: Vector) -> Complex:
    total = c()
    for left, right in zip(v, w, strict=True):
        total = add(total, multiply(conjugate(left), right))
    return total


def leray(mode: Mode, v: Vector) -> Vector:
    norm_squared = Fraction(sum(x * x for x in mode))
    radial = mode_dot(mode, v)
    return [
        add(value, scale(Fraction(-coordinate, 1) / norm_squared, radial))
        for coordinate, value in zip(mode, v, strict=True)
    ]


def negate_mode(mode: Mode) -> Mode:
    return tuple(-x for x in mode)  # type: ignore[return-value]


def main() -> int:
    p = (-1, 0, 3)
    q = (2, -3, -3)
    k = (1, -3, 0)
    assert tuple(p[i] + q[i] for i in range(3)) == k

    velocity: dict[Mode, Vector] = {
        p: [c(3, 3), c(-3, -3), c(1, 1)],
        q: [c(-3), c(), c(-2)],
        k: [c(3, -3), c(1, -1), c()],
    }
    for mode, value in list(velocity.items()):
        velocity[negate_mode(mode)] = [conjugate(z) for z in value]

    modes = list(velocity)
    support = set(modes)

    for mode in modes:
        assert mode_dot(mode, velocity[mode]) == c()
        assert velocity[negate_mode(mode)] == [
            conjugate(z) for z in velocity[mode]
        ]

    nonlinear: dict[Mode, Vector] = {}
    for output in modes:
        raw = [c(), c(), c()]
        for left in modes:
            right = tuple(output[i] - left[i] for i in range(3))
            if right in support:
                raw = vector_add(
                    raw,
                    vector_scale(mode_dot(right, velocity[left]), velocity[right]),
                )
        nonlinear[output] = [minus_i(z) for z in leray(output, raw)]

    def mode_norm_squared(mode: Mode) -> int:
        return sum(x * x for x in mode)

    norms = {
        mode: hermitian(value, value)[0] for mode, value in velocity.items()
    }
    energy = Fraction(1, 2) * sum(norms.values())
    dissipation = sum(
        mode_norm_squared(mode) * norms[mode] for mode in modes
    )

    quadratic_reserve = sum(
        (1 + mode_norm_squared(mode)) ** 3
        * mode_norm_squared(mode)
        * norms[mode]
        for mode in modes
    )
    quartic_reserve = 2 * energy * dissipation
    cubic = sum(
        (1 + mode_norm_squared(mode)) ** 3
        * hermitian(velocity[mode], nonlinear[mode])[0]
        for mode in modes
    )

    assert quadratic_reserve == 8_503_484
    assert quartic_reserve == 245_944
    assert abs(cubic) == 6_111_504

    gap = cubic * cubic - 4 * quadratic_reserve * quartic_reserve
    assert gap == 28_984_957_666_432
    assert gap > 0

    homogeneous_quadratic_reserve = sum(
        mode_norm_squared(mode) ** 3
        * mode_norm_squared(mode)
        * norms[mode]
        for mode in modes
    )
    homogeneous_cubic = sum(
        mode_norm_squared(mode) ** 3
        * hermitian(velocity[mode], nonlinear[mode])[0]
        for mode in modes
    )
    homogeneous_gap = (
        homogeneous_cubic * homogeneous_cubic
        - 4 * homogeneous_quadratic_reserve * quartic_reserve
    )
    assert homogeneous_quadratic_reserve == 7_250_656
    assert abs(homogeneous_cubic) == 5_441_472
    assert homogeneous_gap == 22_476_596_169_728
    assert homogeneous_gap > 0

    print(
        "verified exact zero-coherence H^3 counterexamples: "
        f"A={quadratic_reserve}, B={quartic_reserve}, "
        f"|C|={abs(cubic)}, C^2-4AB={gap}; "
        f"homogeneous A={homogeneous_quadratic_reserve}, "
        f"|C|={abs(homogeneous_cubic)}, "
        f"C^2-4AB={homogeneous_gap}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
