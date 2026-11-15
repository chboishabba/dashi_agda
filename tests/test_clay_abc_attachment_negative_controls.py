"""Negative controls for false Clay endpoint promotions, 2026-11-14.

These tests examine exact elementary arithmetic/logic only. Passing does
not certify any Agda/Lean kernel or a statement about actual zeta zeros.
"""
import sys
import unittest
from fractions import Fraction
from pathlib import Path

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/"scripts"))
import check_clay_abc_attachment_negative_controls as controls

class ClayABCControlsTests(unittest.TestCase):
    def test_rh_false_pole_floor(self):
        self.assertEqual(controls.rh_pole_floor_counterexample()
                         ["local_pole_term"],"-9")

    def test_rh_false_t14_threshold(self):
        r=controls.rh_far_density_threshold_control()
        self.assertEqual(r["t"],15.0)
        self.assertLess(r["proposed_lower_bound"],0)

    def test_rh_first_gamma_sign_not_forced(self):
        r=controls.rh_first_gamma_not_positive_control()
        self.assertEqual(r["first_mode_signed_fifth"],"-3/2")

    def test_ns_r854_conditional_negative_integral(self):
        r=controls.ns_r854_exact_conditional_integral()
        self.assertLess(Fraction(r["strict_conditional_integral_upper"]),0)
        self.assertGreater(Fraction(
            r["initial_negative_alone_positive_integral"]),0)
        self.assertFalse(r["actual_real_ode_rate_certified"])

    def test_bsd_q2_and_correct_original_torsion(self):
        r=controls.bsd_selected_curve_local_controls()
        self.assertEqual(r["v2_x_minus_1"],1)
        self.assertEqual(r["torsion"],((1,1),(-1,-1),(1,2),(-1,-2)))

    def test_ym_tv_not_a_physical_cutoff_estimate(self):
        r=controls.ym_common_carrier_tv_negative_control()
        self.assertEqual(r["same_carrier_tv"],"1/4")
        self.assertEqual(r["nonzero_covariance_mismatch"],"1/16")
        self.assertFalse(r["cutoff_uniform_decay_from_finite_source_alone"])

    def test_no_clay_promotion(self):
        r=controls.run()
        self.assertFalse(r["agda_kernel_checked"])
        self.assertFalse(r["clay_endpoint_proved"])
        self.assertEqual(len(r["claims"]),6)

if __name__=="__main__":
    unittest.main()
