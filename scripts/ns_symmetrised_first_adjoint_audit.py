#!/usr/bin/env python3
"""Exact finite audit of literal and symmetrised partial-adjoint formulas.

The audit uses Gaussian rationals throughout.  It checks the direct T*1,
T*2, swapped-input T*1, and ordered-pair T*1 pairing identities over a
finite transverse battery.  It also supplies an exact scale-parametrised
witness showing that ordered-pair symmetrisation does not create a universal
low-output derivative gain.
"""

from __future__ import annotations

from fractions import Fraction
from typing import Iterable, Tuple

Mode = Tuple[int, int, int]
Gaussian = Tuple[Fraction, Fraction]
Vector = Tuple[Gaussian, Gaussian, Gaussian]

ZERO: Gaussian = (Fraction(0), Fraction(0))
ONE: Gaussian = (Fraction(1), Fraction(0))
I: Gaussian = (Fraction(0), Fraction(1))
MINUS_I: Gaussian = (Fraction(0), Fraction(-1))


def g(value: int | Fraction) -> Gaussian:
    return (Fraction(value), Fraction(0))


def gadd(a: Gaussian, b: Gaussian) -> Gaussian:
    return (a[0] + b[0], a[1] + b[1])


def gneg(a: Gaussian) -> Gaussian:
    return (-a[0], -a[1])


def gmul(a: Gaussian, b: Gaussian) -> Gaussian:
    return (a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0])


def gconj(a: Gaussian) -> Gaussian:
    return (a[0], -a[1])


def vadd(a: Vector, b: Vector) -> Vector:
    return tuple(gadd(x, y) for x, y in zip(a, b))  # type: ignore[return-value]


def vscale(scalar: Gaussian, vector: Vector) -> Vector:
    return tuple(gmul(scalar, value) for value in vector)  # type: ignore[return-value]


def vconj(vector: Vector) -> Vector:
    return tuple(gconj(value) for value in vector)  # type: ignore[return-value]


def mode_vector(mode: Mode) -> Vector:
    return tuple(g(value) for value in mode)  # type: ignore[return-value]


def mode_add(a: Mode, b: Mode) -> Mode:
    return tuple(x + y for x, y in zip(a, b))  # type: ignore[return-value]


def mode_negate(a: Mode) -> Mode:
    return tuple(-x for x in a)  # type: ignore[return-value]


def mode_norm_sq(mode: Mode) -> int:
    return sum(value * value for value in mode)


def bilinear_dot(a: Vector, b: Vector) -> Gaussian:
    total = ZERO
    for x, y in zip(a, b):
        total = gadd(total, gmul(x, y))
    return total


def hermitian_pairing(a: Vector, b: Vector) -> Gaussian:
    return bilinear_dot(vconj(a), b)


def cross_mode(mode: Mode, basis: Mode) -> Mode:
    return (
        mode[1] * basis[2] - mode[2] * basis[1],
        mode[2] * basis[0] - mode[0] * basis[2],
        mode[0] * basis[1] - mode[1] * basis[0],
    )


def leray_project(mode: Mode, vector: Vector) -> Vector:
    norm = mode_norm_sq(mode)
    if norm == 0:
        raise ValueError("Leray projection requires a nonzero mode")
    coefficient = gmul(g(Fraction(1, norm)), bilinear_dot(mode_vector(mode), vector))
    return vadd(vector, vscale(gneg(coefficient), mode_vector(mode)))


def transverse(mode: Mode, vector: Vector) -> bool:
    return bilinear_dot(mode_vector(mode), vector) == ZERO


def transverse_vectors(mode: Mode) -> Iterable[Vector]:
    seen: set[Vector] = set()
    for basis in ((1, 0, 0), (0, 1, 0), (0, 0, 1)):
        raw = cross_mode(mode, basis)
        if raw == (0, 0, 0):
            continue
        real_vector = mode_vector(raw)
        imaginary_vector = vscale(I, real_vector)
        for vector in (real_vector, imaginary_vector):
            if vector not in seen:
                assert transverse(mode, vector)
                seen.add(vector)
                yield vector


def ordered_term(
    k: Mode, p: Mode, q: Mode, u_p: Vector, u_q: Vector
) -> Vector:
    scalar = gmul(MINUS_I, bilinear_dot(u_p, mode_vector(q)))
    return vscale(scalar, leray_project(k, u_q))


def direct_first_adjoint(
    p: Mode, q: Mode, test_k: Vector, u_q: Vector
) -> Vector:
    scalar = gmul(I, hermitian_pairing(u_q, test_k))
    return leray_project(p, vscale(scalar, mode_vector(q)))


def swapped_first_adjoint(
    p: Mode, test_k: Vector, u_q: Vector
) -> Vector:
    scalar = gconj(gmul(MINUS_I, bilinear_dot(u_q, mode_vector(p))))
    return leray_project(p, vscale(scalar, test_k))


def symmetrised_first_adjoint(
    p: Mode, q: Mode, test_k: Vector, u_q: Vector
) -> Vector:
    return vadd(
        direct_first_adjoint(p, q, test_k, u_q),
        swapped_first_adjoint(p, test_k, u_q),
    )


def second_adjoint(
    q: Mode, u_p: Vector, test_k: Vector
) -> Vector:
    scalar = gconj(gmul(MINUS_I, bilinear_dot(u_p, mode_vector(q))))
    return leray_project(q, vscale(scalar, test_k))


def real_pairing(a: Vector, b: Vector) -> Fraction:
    return hermitian_pairing(a, b)[0]


def vector_norm_sq(vector: Vector) -> Fraction:
    return hermitian_pairing(vector, vector)[0]


def verify_pairing_identities() -> int:
    checked = 0
    modes = [
        (1, 0, 0), (0, 1, 0), (0, 0, 1),
        (-1, 0, 0), (0, -1, 0), (0, 0, -1),
        (1, 1, 0), (1, 0, 1), (0, 1, 1),
        (1, -1, 1),
    ]
    for p in modes:
        for q in modes:
            k = mode_add(p, q)
            if k == (0, 0, 0):
                continue
            for u_p in list(transverse_vectors(p))[:2]:
                for u_q in list(transverse_vectors(q))[:2]:
                    for test_k in list(transverse_vectors(k))[:2]:
                        direct_value = real_pairing(
                            test_k, ordered_term(k, p, q, u_p, u_q)
                        )
                        assert direct_value == real_pairing(
                            u_p, direct_first_adjoint(p, q, test_k, u_q)
                        )
                        assert direct_value == real_pairing(
                            u_q, second_adjoint(q, u_p, test_k)
                        )

                        swapped_value = real_pairing(
                            test_k, ordered_term(k, q, p, u_q, u_p)
                        )
                        assert swapped_value == real_pairing(
                            u_p, swapped_first_adjoint(p, test_k, u_q)
                        )

                        ordered_pair_value = direct_value + swapped_value
                        assert ordered_pair_value == real_pairing(
                            u_p,
                            symmetrised_first_adjoint(p, q, test_k, u_q),
                        )
                        checked += 1
    return checked


def symmetrised_no_low_gain_witness(scale: int) -> tuple[Fraction, Fraction]:
    if scale <= 1:
        raise ValueError("scale must exceed one")
    p: Mode = (1, 0, 0)
    q: Mode = (0, scale, 0)
    k = mode_add(p, q)

    u_q: Vector = (ZERO, ZERO, ONE)
    test_k: Vector = (ZERO, ZERO, ONE)
    u_p: Vector = vscale(I, mode_vector(q))

    assert transverse(p, u_p)
    assert transverse(q, u_q)
    assert transverse(k, test_k)

    candidate = symmetrised_first_adjoint(p, q, test_k, u_q)
    expected = vscale(I, mode_vector(q))
    assert candidate == expected

    candidate_norm = vector_norm_sq(candidate)
    low_norm = Fraction(mode_norm_sq(p))
    assert candidate_norm == scale * scale
    assert candidate_norm > scale * low_norm

    ordered_pair_value = (
        real_pairing(test_k, ordered_term(k, p, q, u_p, u_q))
        + real_pairing(test_k, ordered_term(k, q, p, u_q, u_p))
    )
    assert ordered_pair_value == scale * scale

    minus_p = mode_negate(p)
    minus_q = mode_negate(q)
    minus_k = mode_negate(k)
    mate_value = (
        real_pairing(
            vconj(test_k),
            ordered_term(
                minus_k,
                minus_p,
                minus_q,
                vconj(u_p),
                vconj(u_q),
            ),
        )
        + real_pairing(
            vconj(test_k),
            ordered_term(
                minus_k,
                minus_q,
                minus_p,
                vconj(u_q),
                vconj(u_p),
            ),
        )
    )
    assert mate_value == ordered_pair_value
    return candidate_norm, ordered_pair_value + mate_value


def main() -> int:
    checked = verify_pairing_identities()
    norm_sq, reality_fold_value = symmetrised_no_low_gain_witness(37)
    print(
        "verified "
        f"{checked} exact Gaussian-rational transverse pairing cases; "
        "the full ordered-pair first adjoint still has no primitive low gain: "
        f"|T*1_sym|^2={norm_sq}, and the reality-folded signed witness is "
        f"{reality_fold_value}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
