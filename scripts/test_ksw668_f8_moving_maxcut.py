#!/usr/bin/env python3
"""Fail-closed F8 local tests: moving a=t planar positive, compact TT UV control."""
import math
import unittest
import sympy as sp
import ksw668_f8_moving_maxcut as f8

class TestF8(unittest.TestCase):
    def test_01_timelike_boundary(self):
        for t in (1,2,4,6):
            v=-1/math.sqrt(1+t*t)
            self.assertLess(abs(v),1)
            self.assertGreater(1-v*v,0)
    def test_02_angular_local_TT(self):
        mu=sp.symbols('mu',real=True)
        W=(mu**4+6*mu**2+1)/sp.Integer(8)
        coeff=[sp.Rational(2*n+1,2)*sp.integrate(
            W*sp.legendre(n,mu),(mu,-1,1)) for n in (0,2,4)]
        self.assertEqual(coeff,[sp.Rational(2,5),sp.Rational(4,7),sp.Rational(1,35)])
    def test_03_plane_early_receiver_and_far_controls(self):
        r=f8.calc(nX=256,dy=.012,dt=.003)
        self.assertTrue(r['photon_dark'])
        self.assertGreater(r['retarded_tensor_Hyy'],0)
        self.assertGreater(r['intrinsic_4D_electric_Weyl'],0)
        self.assertLess(r['far_to_receiver_ratio'],1e-5)
        self.assertFalse(r['finite_total_3D_perturbation_energy'])
    def test_04_zero_source(self):
        r=f8.calc(nX=128,dy=.02,dt=.005,drive_scale=0)
        self.assertEqual(r['retarded_tensor_Hyy'],0)
        self.assertEqual(r['intrinsic_4D_electric_Weyl'],0)
    def test_05_linearity(self):
        a=f8.calc(nX=128,dy=.02,dt=.005,drive_scale=1)
        b=f8.calc(nX=128,dy=.02,dt=.005,drive_scale=-2)
        self.assertAlmostEqual(b['retarded_tensor_Hyy'],
                               -2*a['retarded_tensor_Hyy'],places=9)
    def test_06_3d_compact_TT_not_certified(self):
        r=f8.calc(nX=256,dy=.012,dt=.003,source_type="compact_3d_TT")
        self.assertTrue(r['finite_total_3D_perturbation_energy'])
        self.assertFalse(r['plane_symmetric_only'])
        self.assertFalse(r['full_B4_gate_closed'])
    def test_07_invalid_geometry_rejected(self):
        with self.assertRaises(ValueError):
            f8.calc(nX=128,dy=.02,dt=.005,eps=.035,inside_chord=.008)
        with self.assertRaises(ValueError):
            f8.calc(nX=65,dy=.02,dt=.005)
    def test_08_no_empirical_promotion(self):
        r=f8.calc(nX=128,dy=.02,dt=.005)
        self.assertFalse(r['observed_graviton_signal'])
        self.assertFalse(r['source_generated_by_matter_action'])
        self.assertFalse(r['verified_refinement_convergence'])

if __name__=="__main__":
    unittest.main(verbosity=2)
