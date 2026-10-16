#!/usr/bin/env python3
from __future__ import annotations

import math
import unittest

import numpy as np

import trinification_two_vev_general_mass_probe as probe


class GeneralTwoVEVMassSpectrumTests(unittest.TestCase):
    def test_equal_unit_specialization(self):
        vals = probe.analytic_spectrum(1.0, 1.0, 1.0, 1.0)
        self.assertEqual(sum(abs(x) < 1e-12 for x in vals), 4)
        positive = [x for x in vals if x > 1e-12]
        self.assertEqual(sum(abs(x - 0.25) < 1e-12 for x in positive), 4)
        self.assertEqual(sum(abs(x - 0.50) < 1e-12 for x in positive), 7)
        self.assertEqual(sum(abs(x - 5.0 / 6.0) < 1e-12 for x in positive), 1)

    def test_random_numeric_eigensystems_match_analytic_formula(self):
        rng = np.random.default_rng(1729)
        for _ in range(32):
            g_l, g_r, v_32, v_33 = 0.2 + 2.0 * rng.random(4)
            numeric = np.linalg.eigvalsh(probe.mass_matrix(g_l, g_r, v_32, v_33))
            analytic = np.asarray(probe.analytic_spectrum(g_l, g_r, v_32, v_33))
            np.testing.assert_allclose(numeric, analytic, atol=2e-11, rtol=2e-11)

    def test_neutral_discriminant_nonnegative_on_positive_samples(self):
        rng = np.random.default_rng(369)
        for _ in range(100):
            g_l, g_r, v_32, v_33 = 0.05 + 4.0 * rng.random(4)
            self.assertGreaterEqual(
                probe.neutral_discriminant(g_l, g_r, v_32, v_33), -1e-10
            )

    def test_four_zero_modes_persist(self):
        vals = probe.analytic_spectrum(0.7, 1.3, 0.9, 1.6)
        self.assertEqual(sum(abs(x) < 1e-12 for x in vals), 4)
        self.assertEqual(sum(x > 1e-12 for x in vals), 12)


if __name__ == "__main__":
    unittest.main()
