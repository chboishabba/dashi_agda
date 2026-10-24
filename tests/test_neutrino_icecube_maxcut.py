"""Numerical/semantic controls for NeutrinoIceCubeMaxCutExact.

This reproduces exact integer arithmetic independently of the Agda module.
It does not constitute an Agda kernel receipt or an IceCube likelihood fit.
"""
from fractions import Fraction
import unittest

PREDICTION = Fraction(1, 31)

# NuFIT 6.1 (2025), normal ordering, IC24 with SK atmospheric data.
# Expressed as integer multiples of 1e-8 eV^2.
SOLAR_LOW, SOLAR_BEST, SOLAR_HIGH = 7236, 7537, 7823
NO_ATM_LOW, NO_ATM_BEST, NO_ATM_HIGH = 245000, 251100, 257600

# NuFIT defines its inverted-ordering atmospheric quantity as delta m^2_32.
# Magnitudes are in the same units; different mass-splitting convention!
IO_ABS_M32_LOW, IO_ABS_M32_HIGH = 242100, 254700
IO_SOLAR_HIGH = 7822

PHASES = ((1, 0), (0, 1), (-1, 0), (0, -1))


def appearance_numerator_sq(real: int, imag: int) -> int:
    return (1 - real) ** 2 + imag**2


def survival_numerator_sq(real: int, imag: int) -> int:
    return (1 + real) ** 2 + imag**2


class NeutrinoMaxCutTests(unittest.TestCase):
    def test_normal_ordering_best_fit_ratio(self):
        self.assertEqual(Fraction(SOLAR_BEST, NO_ATM_BEST),
                         Fraction(7537, 251100))
        self.assertGreater(PREDICTION, Fraction(SOLAR_BEST, NO_ATM_BEST))

    def test_normal_ordering_rectangle_excludes_prediction(self):
        # Treat independent 3sigma projections as a deliberately generous
        # Cartesian rectangle, not as a joint 3sigma confidence statement.
        conservative_upper = Fraction(SOLAR_HIGH, NO_ATM_LOW)
        self.assertEqual(31 * SOLAR_HIGH, 242513)
        self.assertEqual(NO_ATM_LOW - 31 * SOLAR_HIGH, 2487)
        self.assertGreater(PREDICTION, conservative_upper)

    def test_inverted_ordering_convention(self):
        # delta m31^2 = delta m32^2 + delta m21^2.
        # For IO, delta m32^2 < 0, delta m31^2 is also < 0.
        delta_m31 = -IO_ABS_M32_LOW + IO_SOLAR_HIGH
        self.assertLess(delta_m31, 0)
        signed_ratio = Fraction(IO_SOLAR_HIGH, delta_m31)
        self.assertLess(signed_ratio, 0)
        # Absolute-magnitude ratio is a different hypothesis and is NOT
        # excluded by the broad marginal IO interval rectangle.
        max_abs_ratio = Fraction(IO_SOLAR_HIGH, -delta_m31)
        self.assertLess(PREDICTION, max_abs_ratio)

    def test_inverted_ordering_absolute_ratio_rectangle_witness(self):
        # Independent marginal IO intervals (units 1e-8 eV^2).
        solar, abs_m32 = 7600, 243200
        self.assertTrue(7236 <= solar <= 7822)
        self.assertTrue(242100 <= abs_m32 <= 254700)
        abs_m31 = abs_m32 - solar
        self.assertEqual(abs_m31, 235600)
        self.assertEqual(Fraction(solar, abs_m31), PREDICTION)
        # Positive magnitude match is not a signed m31 ratio match,
        # a joint-confidence statement, or a model fit.
        self.assertEqual(Fraction(solar, -abs_m31), -PREDICTION)

    def test_four_phase_two_flavour_probability_conservation(self):
        for real, imag in PHASES:
            self.assertEqual(real**2 + imag**2, 1)
            self.assertEqual(appearance_numerator_sq(real, imag) +
                             survival_numerator_sq(real, imag), 4)
        self.assertEqual([appearance_numerator_sq(*x) for x in PHASES],
                         [0, 2, 4, 2])

    def test_phase_quarter_turn_is_order_four(self):
        for phase in range(4):
            self.assertEqual((phase + 4) % 4, phase)


if __name__ == "__main__":
    unittest.main()
