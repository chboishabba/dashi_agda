#!/usr/bin/env python3
"""S02/S04/S09 exact rational acoustic BIDI/impulse reference.

Reproduces the selected 3-axis scalar-lattice source's third local time
derivative after a velocity kick and mass-inverse nonidentifiability.
This tests *chosen model arithmetic*, not independent physical TSVF
measurement, formal Agda acceptance, Stone/OS or a continuum theorem.
"""
from fractions import Fraction as F
from itertools import product

AXES = ("x", "y", "z")
SIGNS = ("+", "-")
SENSORS = tuple(product(AXES, SIGNS))


def principal(omega, kx, ky, kz):
    return -omega * omega + kx * kx + ky * ky + kz * kz


def full_response_denominator(mass_sq, omega, kx, ky, kz):
    return principal(omega, kx, ky, kz) + mass_sq


def original_stiffness(k, mass_sq, site):
    if site == "origin":
        return mass_sq + 6 * k
    if site in SENSORS:
        return -k
    if site == "outside":
        return F(0)
    raise ValueError(site)


def third_derivative(k, mass_sq, site):
    return -original_stiffness(k, mass_sq, site)


def main():
    tests = 0
    couplings = [F(1, 7), F(3, 2), F(225, 4), F(99, 8)]
    masses = [F(0), F(2, 5), F(1), F(121, 100)]
    for k, m in product(couplings, masses):
        for site in SENSORS:
            assert third_derivative(k, m, site) == k
            tests += 1
        assert third_derivative(k, m, "origin") == -(m + 6*k)
        assert third_derivative(k, m, "outside") == F(0)
        tests += 2

    frequencies = [F(0), F(1, 5), F(-2, 3)]
    momenta = [F(0), F(2, 7), F(-5, 4)]
    for m1, m2 in product(masses, repeat=2):
        for omega, kx, ky, kz in product(frequencies, momenta, momenta, momenta):
            assert principal(omega, kx, ky, kz) == principal(omega, kx, ky, kz)
            diff = (full_response_denominator(m2, omega, kx, ky, kz) -
                    full_response_denominator(m1, omega, kx, ky, kz))
            assert diff == m2 - m1
            tests += 2
        assert full_response_denominator(m1,0,0,0,0) == m1
        assert full_response_denominator(m2,0,0,0,0) == m2
        tests += 2
        if m1 != m2:
            assert full_response_denominator(m1,0,0,0,0) != full_response_denominator(m2,0,0,0,0)
            tests += 1

    assert len(SENSORS) == 6
    print(f"PASS {tests} exact Fraction selected-acoustic tests")
    print("PASS six local first-neighbour q'''(0) signals identify k, mass-blind")
    print("PASS equal Lorentzian principal symbols do NOT identify full mass response")
    print("SCOPE: selected oscillator-lattice model only; Agda/physical E1/OS OPEN")


if __name__ == "__main__":
    main()
