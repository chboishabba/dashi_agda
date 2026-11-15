#!/usr/bin/env python3
import unittest
from ksw668_f8_moving_neumann_characteristic import exact,bound
class TestOriginalMovingNeumann(unittest.TestCase):
    def test_original_boundary(self):
        for t in (1,4/3,2):self.assertTrue(exact(t)["original_Israel_boundary_exact"])
    def test_rational_slice(self):
        d=exact(4/3,1/8,1/12)
        self.assertAlmostEqual(d["q_minus"],-7/96)
        self.assertAlmostEqual(d["beta"],.25)
    def test_full_interval_beta(self):
        self.assertLess(bound()["upper"],.382)
    def test_zero_boundary_source(self):
        r=exact(1.5,1,0)
        self.assertAlmostEqual(r["q_minus"],r["beta"])
    def test_forced_incoming(self):
        self.assertGreater(exact(2,1,1)["q_minus_advection_velocity"],0)
    def test_original_boundary_flux_factor(self):
        self.assertTrue(bound()["homogeneous_flux_ratio_equals_beta"])
    def test_no_global_promotion(self):
        self.assertFalse(bound()["actual_global_source_to_receiver_FIO"])
    def test_invalid_time(self):
        with self.assertRaises(ValueError):exact(3)
if __name__=="__main__":unittest.main(verbosity=2)
