#!/usr/bin/env python3
"""Local-only brane original max-cut: positive controls + non-promotion negatives."""
import math
import unittest
import ksw668_brane_original_maxcut_exact as core
import ksw668_ads5_induced_weyl_receiver_partial as curvature

class BraneOriginalMaxCutTest(unittest.TestCase):
    def test_genuine_codimension_one_brane_emitter(self):
        for delta in (.005,.02,.04):
            x=core.early_thin_receiver(delta=delta)
            self.assertLess(x['positive_lower'],x['receiver'])
            self.assertLess(x['receiver'],x['positive_upper'])
            self.assertLess(x['receiver_time'],x['photon_time'])
            self.assertFalse(x['self_gravitating_metric_used'])

    def test_fail_closed_outside_early_window(self):
        for kwargs in ({'t':1.9},{'t':math.pi},{'delta':-.01}):
            with self.assertRaises(AssertionError):
                core.early_thin_receiver(**kwargs)

    def test_static_winding_not_a_stability_proof(self):
        x=core.static_z2_winding()
        self.assertFalse(x['coupled_stability'])
        self.assertIn('1/(kappa5² R)',x['tuning'])

    def test_israel_not_unjustified_robin(self):
        x=core.linear_TT_israel()
        self.assertEqual(x['original_kappa5_squared'],6)
        self.assertFalse(x['extra_robin_on_dimensionless_H'])
        self.assertFalse(x['localized_source'])

    def test_energy_boundary_sign_indefinite(self):
        import sympy as s
        ht,g,v,b=s.symbols('ht g v b',real=True)
        E=v*((1-v*v)*ht**2-g**2)/(2*b**3)
        self.assertLess(E.subs({ht:1,g:0,v:-s.Rational(1,2),b:1}),0)
        self.assertGreater(E.subs({ht:0,g:1,v:-s.Rational(1,2),b:1}),0)
        self.assertFalse(core.moving_energy_zero_mode()['strict_gap'])

    def test_gauge_invariant_mode_not_retarded_message(self):
        x=curvature.audit()
        self.assertGreater(abs(x['manufactured_plus_electric_Weyl']),.008)
        self.assertFalse(x['retarded_localized_source'])
        self.assertFalse(x['observed_early_physical_signal'])

if __name__=='__main__':
    unittest.main(verbosity=2)
