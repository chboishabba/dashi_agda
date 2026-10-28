#!/usr/bin/env python3
"""Exact-rational finite P3 lattice spectral algebra; no AA/GR promotion.

This *synthetic* operator H = -J * adjacency(P3) + D*diag(0,1,2)
is not the quasi-periodic Aubry–André operator. In particular D is a
chosen site gradient, not the Ma et al. lattice Δ or a measured tilt.
Source: Aubry/André 1980 model distinction; Ma et al. arXiv:2610.17499v2.
The existing DASHI Agda P3 operator no-go remains the theorem owner.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import json


Matrix3 = tuple[tuple[Fraction, Fraction, Fraction], ...]


def make_matrix(hopping: Fraction, gradient: Fraction) -> Matrix3:
    j, d = Fraction(hopping), Fraction(gradient)
    return (
        (Fraction(0), -j, Fraction(0)),
        (-j, d, -j),
        (Fraction(0), -j, 2 * d),
    )


def determinant3(m: Matrix3) -> Fraction:
    a, b, c = m
    return (
        a[0] * (b[1] * c[2] - b[2] * c[1])
        - a[1] * (b[0] * c[2] - b[2] * c[0])
        + a[2] * (b[0] * c[1] - b[1] * c[0])
    )


def trace_square(m: Matrix3) -> Fraction:
    return sum(m[i][j] * m[j][i] for i in range(3) for j in range(3))


def characteristic_coefficients(m: Matrix3) -> tuple[Fraction, Fraction, Fraction, Fraction]:
    """Return coefficients of monic det(lambda I - H), cubic to constant."""
    tr = sum(m[i][i] for i in range(3))
    c2 = (tr * tr - trace_square(m)) / 2
    return (Fraction(1), -tr, c2, -determinant3(m))


def polynomial_eval(coefficients, x: Fraction) -> Fraction:
    value = Fraction(0)
    for coefficient in coefficients:
        value = value * x + coefficient
    return value


def expected_coefficients(hopping: Fraction, gradient: Fraction):
    """(lambda-D)*((lambda-D)^2 - (D^2+2*J^2))."""
    j, d = Fraction(hopping), Fraction(gradient)
    return (Fraction(1), -3*d, 2*d*d-2*j*j, 2*d*j*j)


def analyze(hopping: Fraction = Fraction(1), gradient: Fraction = Fraction(2)):
    m = make_matrix(hopping, gradient)
    calculated = characteristic_coefficients(m)
    expected = expected_coefficients(hopping, gradient)
    if calculated != expected:
        raise AssertionError("exact three-site characteristic identity failed")
    if polynomial_eval(calculated, gradient) != 0:
        raise AssertionError("central exact eigenvalue not reproduced")
    if m[0][1] != m[1][0] or m[1][2] != m[2][1]:
        raise AssertionError("non-symmetric P3 operator")
    return {
        "scope": "synthetic finite signed three-site lattice only",
        "hopping": str(hopping),
        "site_gradient": str(gradient),
        "characteristic_cubic": list(map(str, calculated)),
        "exact_central_eigenvalue": str(gradient),
        "nonzero_hopping": hopping != 0,
        "experimental_aubry_andre_transition_proven": False,
        "quasiperiodicity_constructed": False,
        "clock_coherence_calibrated": False,
        "r2p2_yb_clock_observed": False,
        "quantum_gravity_claimed": False,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--hopping", default="1", help="exact rational toy J")
    parser.add_argument("--site-gradient", default="2", help="exact rational toy D")
    args = parser.parse_args()
    result = analyze(Fraction(args.hopping), Fraction(args.site_gradient))
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
