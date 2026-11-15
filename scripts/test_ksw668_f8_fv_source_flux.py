#!/usr/bin/env python3
import unittest
import numpy as np
from ksw668_f8_fv_source_flux import (
 exact_cell_averages,total_scaled_moments,cell_mass)
from ksw668_f8_tt_multipole import averaged_sources
class ExactSourceFlux(unittest.TestCase):
    def test_monopole_zero(self):self.assertEqual(total_scaled_moments()['l0'],0)
    def test_quadrupole_zero(self):self.assertEqual(total_scaled_moments()['l2'],0)
    def test_ell4_nonzero(self):self.assertGreater(total_scaled_moments()['l4'],0)
    def test_ell4_analytic(self):self.assertAlmostEqual(total_scaled_moments()['l4'],total_scaled_moments()['l4_analytic'],places=11)
    def test_independent_96_point_gauss(self):
        for dr in (.012,.008):
            r=np.arange(12)*dr
            a=exact_cell_averages(.04,r,dr)
            b=averaged_sources(.04,r,dr,quad_nodes=96)
            self.assertLess(np.max(abs(a-b))/np.max(abs(b)),2e-8)
    def test_support(self):
        r=np.arange(30)*.005
        a=exact_cell_averages(.04,r,.005)
        self.assertEqual(np.max(abs(a[:,r>.045])),0)
    def test_finite(self):self.assertTrue(np.isfinite(exact_cell_averages(.04,np.arange(15)*.006,.006)).all())
    def test_weighted_cell_mass_reconstruction(self):
        eps=.04;dr=.006;r=np.arange(24)*dr;a=exact_cell_averages(eps,r,dr)
        for q,ell in enumerate((0,2,4)):
            d=3+2*ell;w=((r+dr/2)**d-np.maximum(r-dr/2,0)**d)/d
            self.assertAlmostEqual(np.dot(w,a[q])/eps**d,total_scaled_moments()['l'+str(ell)],places=10)
    def test_bad_cell(self):
        with self.assertRaises(ValueError):cell_mass(0,.8,.7)
    def test_bad_scale(self):
        with self.assertRaises(ValueError):exact_cell_averages(0,np.arange(5),.1)
if __name__=='__main__':unittest.main(verbosity=2)
