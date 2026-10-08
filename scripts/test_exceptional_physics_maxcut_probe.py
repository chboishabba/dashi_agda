from fractions import Fraction
import unittest

import sympy as sp

from scripts.exceptional_physics_maxcut_probe import verify


class ExceptionalPhysicsMaxCutProbeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.out = verify()

    def test_first_tits_basis_structure_constants(self):
        self.assertEqual(
            self.out["basis_pair_support"],
            {0: 414, 1: 291, 2: 24, "other": 0},
        )

    def test_exceptional_poisson_values(self):
        self.assertEqual(
            self.out["poisson_values"],
            {
                sp.Rational(-11, 54): 12,
                sp.Rational(2, 27): 6,
                sp.Rational(5, 27): 3,
                sp.Rational(13, 54): 6,
            },
        )

    def test_trinification_hypercharge_anomaly_checks(self):
        self.assertEqual(self.out["hypercharge_sum"], Fraction(0, 1))
        self.assertEqual(self.out["hypercharge_cube_sum"], Fraction(0, 1))

    def test_metric_is_nonflat(self):
        self.assertEqual(self.out["ricci_scalar_x100"], sp.Rational(787320, 300763))
        self.assertEqual(self.out["einstein00_x100"], sp.Rational(24273, 17956))

    def test_measured_physionet_discriminator_separates(self):
        self.assertGreater(self.out["physionet_subject1_log_distance"], 2.0)
        self.assertAlmostEqual(
            self.out["physionet_subject1_log_distance"],
            2.279858209762054,
            places=12,
        )
        self.assertAlmostEqual(
            self.out["physionet_time_origin_minutes"],
            20.0127,
            places=10,
        )


if __name__ == "__main__":
    unittest.main()
