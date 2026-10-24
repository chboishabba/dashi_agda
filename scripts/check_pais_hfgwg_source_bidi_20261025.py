#!/usr/bin/env python3
"""Bounded SI null checks for Pais HFGWG / Gertsenshtein source review.

Source hierarchy:
- Gertsenshtein (1962): physical photon-graviton conversion mechanism.
- JASON JSR-08-506 (2008) section 3.3: idealised weak-conversion ratio.
- Pais US10322827B2 (2019), description equations 4 and correction.
This is a classical order-of-magnitude model, NOT a patent implementation,
an observed GW emission result, or an exact account of a physical cavity.
"""
import math
import unittest

G = 6.67430e-11                   # m^3 kg^-1 s^-2
C = 299_792_458.0                 # m s^-1
MU0 = 1.25663706127e-6           # N A^-2, approximate modern SI value
EPS0 = 1.0 / (MU0 * C * C)       # F m^-1


def _check_nonnegative(name, value):
    if isinstance(value, bool) or not isinstance(value, (float, int)):
        raise ValueError(f"{name} must be a finite nonnegative SI number")
    value = float(value)
    if not math.isfinite(value) or value < 0:
        raise ValueError(f"{name} must be a finite nonnegative SI number")
    return value


def gertsenshtein_illustrative_fraction(B_tesla, L_m):
    """Weak-conversion SI dimensional restoration of JASON/Pais scaling.

    The 4*pi prefactor reflects the patent's cited expression and a selected
    convention, not a universal cavity-geometry or polarisation coefficient.
    Do not extrapolate this perturbative formula to extreme fields.
    """
    B = _check_nonnegative("B_tesla", B_tesla)
    L = _check_nonnegative("L_m", L_m)
    return (4.0 * math.pi * G / (MU0 * C**4)) * (B * L)**2


def illustrative_gw_power(P_em_watt, B_tesla, L_m):
    P = _check_nonnegative("P_em_watt", P_em_watt)
    return P * gertsenshtein_illustrative_fraction(B_tesla, L_m)


def magnetic_field_energy_density(B_tesla):
    B = _check_nonnegative("B_tesla", B_tesla)
    return B * B / (2.0 * MU0)


def _vector(v):
    if len(v) != 3:
        raise ValueError("field vector must have three components")
    ans = tuple(float(x) for x in v)
    if not all(math.isfinite(x) for x in ans):
        raise ValueError("field vector components must be finite")
    return ans


def em_energy_density(E_v_m, B_tesla):
    E, B = _vector(E_v_m), _vector(B_tesla)
    return 0.5 * (EPS0 * sum(x*x for x in E) +
                  sum(x*x for x in B) / MU0)


def em_cross_energy_density(E1, B1, E2, B2):
    """Ordinary Maxwell cross term: not an anomalous field coupling."""
    E1, B1, E2, B2 = tuple(_vector(x) for x in (E1, B1, E2, B2))
    dot = lambda a, b: sum(x*y for x, y in zip(a, b))
    return EPS0 * dot(E1, E2) + dot(B1, B2) / MU0


class SourceBoundedTests(unittest.TestCase):
    def test_single_metre_fourteen_tesla(self):
        self.assertAlmostEqual(
            gertsenshtein_illustrative_fraction(14.0, 1.0),
            1.61949265759e-35, delta=1e-45)
        self.assertAlmostEqual(
            illustrative_gw_power(1e6, 14.0, 1.0),
            1.61949265759e-29, delta=1e-39)

    def test_zero_and_scaling(self):
        self.assertEqual(gertsenshtein_illustrative_fraction(0, 1), 0)
        self.assertEqual(gertsenshtein_illustrative_fraction(14, 0), 0)
        f = gertsenshtein_illustrative_fraction(7, 1)
        self.assertAlmostEqual(gertsenshtein_illustrative_fraction(14, 1), 4*f)
        self.assertAlmostEqual(gertsenshtein_illustrative_fraction(7, 2), 4*f)

    def test_large_field_energy_is_not_gw_detection(self):
        self.assertAlmostEqual(
            magnetic_field_energy_density(1e10),
            3.97887357782e25, delta=1e14)

    def test_maxwell_superposition_cross_term(self):
        E1, E2 = (12., 0., 0.), (3., 0., 0.)
        B1, B2 = (0., .2, 0.), (0., .4, 0.)
        Et = tuple(x+y for x, y in zip(E1, E2))
        Bt = tuple(x+y for x, y in zip(B1, B2))
        lhs = em_energy_density(Et, Bt)
        rhs = (em_energy_density(E1, B1) +
               em_energy_density(E2, B2) +
               em_cross_energy_density(E1, B1, E2, B2))
        self.assertAlmostEqual(lhs, rhs, places=10)
        self.assertEqual(
            em_cross_energy_density((1,0,0), (0,0,0),
                                    (0,1,0), (0,0,0)), 0)

    def test_fail_closed_inputs(self):
        for bad in (-1, math.nan, math.inf, True):
            with self.assertRaises(ValueError):
                gertsenshtein_illustrative_fraction(bad, 1)
        with self.assertRaises(ValueError):
            em_energy_density((1, 2), (1, 2, 3))


if __name__ == "__main__":
    print("Only bounded, classical illustrative source-model checks; no GW observed.")
    unittest.main()
