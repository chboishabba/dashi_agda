#!/usr/bin/env python3
import unittest,math
from ksw668_f8_forced_moving_neumann_energy import symbolic,bound
class TestOriginalMovingEnergy(unittest.TestCase):
    def test_square_completion(self):
        self.assertTrue(symbolic()["energy_square_completion_exact"])
    def test_wall_lifting(self):
        self.assertTrue(symbolic()["sourced_moving_wall_lift_exact"])
    def test_coercivity(self):
        self.assertGreater(bound()["coercive_factor"],0)
    def test_finite_inhom_energy(self):
        self.assertTrue(math.isfinite(bound()["E_upper_when_weighted_force_norm_below_one"]))
    def test_original_T_interval(self):
        self.assertAlmostEqual(bound()["original_Poincare_T_duration"],.85844146178,delta=1e-8)
    def test_compact_force_finite(self):
        self.assertTrue(bound()["finite_weighted_force_for_compact_smooth_G"])
    def test_not_weyl(self):
        self.assertFalse(bound()["nonzero_original_receiver_Weyl_proved"])
if __name__=='__main__':unittest.main(verbosity=2)
