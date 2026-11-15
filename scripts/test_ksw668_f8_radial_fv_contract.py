#!/usr/bin/env python3
import unittest
import numpy as np
from ksw668_f8_radial_fv_contract import (
 coefficients,old_coefficients,apply_radial,discrete_green_energy,audit)
class ExactRadialFiniteVolume(unittest.TestCase):
    def test_all_dimensions(self):self.assertEqual([x['d'] for x in audit()['rows']],[3,7,11])
    def test_first_cell_3d(self):self.assertAlmostEqual(3*coefficients(3,1)[0]-coefficients(3,1)[1],6)
    def test_first_cell_7d(self):self.assertAlmostEqual(3*coefficients(7,1)[0]-coefficients(7,1)[1],14)
    def test_first_cell_11d(self):self.assertAlmostEqual(3*coefficients(11,1)[0]-coefficients(11,1)[1],22)
    def test_legacy_3d_counterexample(self):self.assertAlmostEqual(3*old_coefficients(3,1)[0]-old_coefficients(3,1)[1],6.5)
    def test_legacy_7d_counterexample(self):self.assertGreater(3*old_coefficients(7,1)[0]-old_coefficients(7,1)[1],34)
    def test_legacy_11d_counterexample(self):self.assertGreater(3*old_coefficients(11,1)[0]-old_coefficients(11,1)[1],172)
    def test_constant_harmonic(self):
        for d in (3,7,11):self.assertTrue(np.allclose(apply_radial(d,np.ones(12))[:-1],0))
    def test_global_quadratic(self):
        for d in (3,7,11):self.assertTrue(np.allclose(apply_radial(d,np.arange(12.)**2)[:-1],2*d))
    def test_weighted_energy(self):
        for d in (3,7,11):
            u=np.sin(.7*np.arange(12.));u[-1]=0
            a,b=discrete_green_energy(d,u)
            self.assertLess(b,0);self.assertAlmostEqual(a/b,1,places=12)
    def test_reject_bad_d(self):
        with self.assertRaises(ValueError):coefficients(1,1)
    def test_reject_nonzero_outer_dirichlet(self):
        with self.assertRaises(ValueError):discrete_green_energy(3,np.ones(12))
    def test_no_physical_promotion(self):self.assertFalse(audit()['physical_retarded_Weyl_convergence'])
if __name__=='__main__':unittest.main(verbosity=2)
