#!/usr/bin/env python3
"""Nine original a=t frozen symbol positive and negative tests."""
import unittest
from ksw668_f8_frozen_oblique_neumann import (
  symbol,frozen_finite,uniform_original_high_s,low_frequency_counterexample)
class TestOriginalFrozenOblique(unittest.TestCase):
    def test_exact_oblique_factor(self):
        for t in (1,1.5,2):
            d=symbol(t,16,2)
            self.assertAlmostEqual(d["boundary_factor_A"]*d["exact_frozen_oblique_inverse"],1)
    def test_strict_Bessel_bound(self):
        for s in (.01,.1,1,16,64):
            d=symbol(1,s,0)
            self.assertLess(abs(d["residual_multiplier_R"]),d["upper_bound_on_abs_R"])
    def test_uniform_high_s(self):
        d=uniform_original_high_s()
        self.assertLess(d["uniform_rho"],1)
        self.assertLess(d["uniform_residual_bound"],1e-6)
    def test_low_s_counterexample(self):
        self.assertGreater(low_frequency_counterexample()["abs_residual"],1)
    def test_exact_finite_telescope(self):
        for n in (0,1,2,16,128):
            d=frozen_finite(depth=n)
            self.assertAlmostEqual(d["residual_from_operator"],d["exact_residual_power"],delta=2e-12)
    def test_no_moving_promotion(self):
        self.assertFalse(uniform_original_high_s()["actual_time_dependent_boundary_FIO"])
    def test_no_receiver_promotion(self):
        self.assertFalse(frozen_finite()["nonzero_original_receiver_Weyl_proved"])
    def test_invalid_params(self):
        for triple in ((.5,1,0),(1,-1,0),(1,1,-.1)):
            with self.assertRaises(ValueError): symbol(*triple)
    def test_no_fake_uniform_threshold(self):
        with self.assertRaises(ValueError):uniform_original_high_s(5)
if __name__=="__main__":unittest.main(verbosity=2)
