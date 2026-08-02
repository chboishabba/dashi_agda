#!/usr/bin/env python3
"""Exact Fourier trilinear antisymmetry and no-bypass audit."""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from itertools import product
from typing import Iterable, Tuple

Q = Fraction
ComplexQ = Tuple[Q, Q]
VectorQ = Tuple[ComplexQ, ComplexQ, ComplexQ]
Mode = Tuple[int, int, int]
ZERO: ComplexQ = Q(0), Q(0)
MINUS_I: ComplexQ = Q(0), Q(-1)


def cadd(a: ComplexQ, b: ComplexQ) -> ComplexQ:
    return a[0] + b[0], a[1] + b[1]


def cneg(a: ComplexQ) -> ComplexQ:
    return -a[0], -a[1]


def cmul(a: ComplexQ, b: ComplexQ) -> ComplexQ:
    return a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0]


def cconj(a: ComplexQ) -> ComplexQ:
    return a[0], -a[1]


def vscale(scalar: ComplexQ, vector: VectorQ) -> VectorQ:
    return tuple(cmul(scalar, value) for value in vector)  # type: ignore[return-value]


def vconj(vector: VectorQ) -> VectorQ:
    return tuple(cconj(value) for value in vector)  # type: ignore[return-value]


def add_mode(a: Mode, b: Mode) -> Mode:
    return tuple(x + y for x, y in zip(a, b))  # type: ignore[return-value]


def negate_mode(a: Mode) -> Mode:
    return tuple(-x for x in a)  # type: ignore[return-value]


def integer_dot(a: Mode, b: Mode) -> int:
    return sum(x * y for x, y in zip(a, b))


def cross(a: Mode, b: Mode) -> Mode:
    return (
        a[1] * b[2] - a[2] * b[1],
        a[2] * b[0] - a[0] * b[2],
        a[0] * b[1] - a[1] * b[0],
    )


def bilinear_mode_dot(vector: VectorQ, mode: Mode) -> ComplexQ:
    result = ZERO
    for value, coordinate in zip(vector, mode):
        result = cadd(result, (value[0] * coordinate, value[1] * coordinate))
    return result


def hermitian_pairing(left: VectorQ, right: VectorQ) -> ComplexQ:
    result = ZERO
    for x, y in zip(left, right):
        result = cadd(result, cmul(cconj(x), y))
    return result


def leray_project(mode: Mode, vector: VectorQ) -> VectorQ:
    norm_squared = integer_dot(mode, mode)
    if norm_squared == 0:
        raise ValueError("nonzero output mode required")
    dot_value = bilinear_mode_dot(vector, mode)
    coefficient = dot_value[0] / norm_squared, dot_value[1] / norm_squared
    longitudinal = tuple(
        cmul((Q(coordinate), Q(0)), coefficient) for coordinate in mode
    )
    return tuple(
        cadd(value, cneg(parallel))
        for value, parallel in zip(vector, longitudinal)
    )  # type: ignore[return-value]


def trilinear(
    transport_mode: Mode,
    transport: VectorQ,
    advected_mode: Mode,
    advected: VectorQ,
    output_mode: Mode,
    test: VectorQ,
) -> Q:
    assert add_mode(transport_mode, advected_mode) == output_mode
    coefficient = cmul(MINUS_I, bilinear_mode_dot(transport, advected_mode))
    nonlinear = leray_project(output_mode, vscale(coefficient, advected))
    return hermitian_pairing(test, nonlinear)[0]


def transverse_vector(mode: Mode, seed_a: Mode, seed_b: Mode, phase: int) -> VectorQ:
    first, second = cross(mode, seed_a), cross(mode, seed_b)
    scalar_a, scalar_b = (Q(phase), Q(phase + 1)), (Q(phase - 2), Q(1 - phase))
    return tuple(
        cadd(cmul(scalar_a, (Q(x), Q(0))), cmul(scalar_b, (Q(y), Q(0))))
        for x, y in zip(first, second)
    )  # type: ignore[return-value]


def nonzero_modes(bound: int) -> Iterable[Mode]:
    for mode in product(range(-bound, bound + 1), repeat=3):
        if mode != (0, 0, 0):
            yield mode  # type: ignore[misc]


@dataclass(frozen=True)
class AntisymmetryAudit:
    cases: int
    nonzero_cases: int


def verify_trilinear_antisymmetry(bound: int = 2) -> AntisymmetryAudit:
    checked = nonzero = 0
    seed_pairs = (((1, 0, 0), (0, 1, 0)), ((0, 1, 0), (0, 0, 1)))
    for p in nonzero_modes(bound):
        for q in nonzero_modes(bound):
            k = add_mode(p, q)
            if k == (0, 0, 0):
                continue
            u = transverse_vector(p, *seed_pairs[0], phase=1)
            v = transverse_vector(q, *seed_pairs[1], phase=2)
            w = transverse_vector(k, *seed_pairs[0], phase=3)
            direct = trilinear(p, u, q, v, k, w)
            swapped = trilinear(
                p, u, negate_mode(k), vconj(w), negate_mode(q), vconj(v)
            )
            assert direct == -swapped
            checked += 1
            nonzero += direct != 0
    return AntisymmetryAudit(checked, nonzero)


def verify_no_second_adjoint_bypass(scale: int = 37) -> None:
    p, q = (1, 0, 0), (0, scale, 0)
    k = add_mode(p, q)
    assert integer_dot(p, p) == 1
    assert integer_dot(q, q) == scale * scale
    assert integer_dot(k, k) == scale * scale + 1
    assert integer_dot(q, q) > scale * integer_dot(p, p)
    assert integer_dot(k, k) > scale * integer_dot(p, p)


def main() -> int:
    audit = verify_trilinear_antisymmetry()
    verify_no_second_adjoint_bypass()
    print(
        f"verified {audit.cases} exact Fourier trilinear antisymmetry cases "
        f"({audit.nonzero_cases} nonzero) and the scale-37 no-bypass ordering"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
