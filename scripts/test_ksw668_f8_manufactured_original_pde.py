#!/usr/bin/env python3
import unittest
from ksw668_f8_manufactured_original_pde import check
class OriginalMovingManufactured(unittest.TestCase):
    def test_three_regular_radial_modes(self):self.assertEqual(check()['effective_dimensions'],[3,7,11])
    def test_exact_semidiscrete_wave(self):self.assertTrue(check()['semidiscrete_manufactured_consistency'])
    def test_original_Israel(self):self.assertTrue(check()['original_moving_Israel_exact'])
    def test_dU(self):self.assertLess(check()['max_err_dU'],1e-9)
    def test_dP(self):self.assertLess(check()['max_err_dP'],1e-9)
    def test_dM(self):self.assertLess(check()['max_err_dM'],1e-9)
    def test_other_radial_grid(self):self.assertTrue(check(dr=.012,dy=.011,ny=10,nr=22)['semidiscrete_manufactured_consistency'])
    def test_original_t_rational(self):self.assertTrue(check(t=4/3,T=.4)['semidiscrete_manufactured_consistency'])
    def test_not_physical_source(self):self.assertFalse(check()['compact_physical_source'])
    def test_no_receiver_promotion(self):self.assertFalse(check()['receiver_Weyl_convergence'])
    def test_firstorder_SBP_moving_Israel(self):
        self.assertTrue(check(normal_order=1)['semidiscrete_manufactured_consistency'])
        self.assertTrue(check(normal_order=1,t=4/3)['original_moving_Israel_exact'])
if __name__=='__main__':unittest.main(verbosity=2)
