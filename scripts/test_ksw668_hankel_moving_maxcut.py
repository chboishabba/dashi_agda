#!/usr/bin/env python3
"""Eight locally accepted non-promotion tests for Hankel/KK and moving lift."""
import unittest
import ksw668_hankel_moving_maxcut as a

class HankelBraneMaxcut(unittest.TestCase):
    def test_resolvent_exact_ODE(self):
        r=a.verify_resolvent_symbolic()
        self.assertTrue(r['normal_derivative_exact'])
    def test_static_resolvent_laplace_decay(self):
        near=a.stationary_outgoing(z=1)
        far=a.stationary_outgoing(z=10)
        self.assertLess(abs(far['transfer']),abs(near['transfer']))
        self.assertLess(near['boundary_impedance'],0)
    def test_bessel_neumann_wronskian(self):
        for m in [.1,.35,1.1,3.0,9.0]:
            r=a.normalized_modes(b=1,m=m,z=1)
            self.assertAlmostEqual(r['continuum_Hz'],0,delta=1e-9)
            self.assertAlmostEqual(r['continuum_H'],r['continuum_at_b'],delta=1e-9)
    def test_zero_mode_normalized(self):
        r=a.normalized_modes()
        self.assertAlmostEqual(r['zero_H']**2/2,1)
    def test_KK_spectral_packet_finite(self):
        r=a.finite_energy_packet()
        self.assertGreater(r['finite_spectral_mass_energy'],0)
        self.assertFalse(r['moving_source_reception_proved'])
    def test_moving_boundary_data_exact_lift(self):
        r=a.moving_boundary_lift()
        self.assertTrue(r['exact_oblique_boundary_lift'])
        self.assertFalse(r['Green_operator_constructed'])
    def test_wrong_sign_or_zero_source_forbidden(self):
        with self.assertRaises(ValueError):a.stationary_outgoing(laplace_s=-1)
        with self.assertRaises(ValueError):a.finite_energy_packet(mlo=-1)
    def test_moving_abstract_retarded_theorem_and_strict_chord(self):
        r=a.moving_abstract_green_and_bulk_chord()
        self.assertTrue(r['abstract_smooth_retarded_operator_established_by_theorem'])
        self.assertTrue(r['same_metric_causal_chord_interiors'])
        self.assertFalse(r['nonzero_electric_Weyl_from_retarded_source_proved'])
    def test_no_physical_promotion(self):
        r=a.audit()
        self.assertFalse(r['explicit_original_moving_retarded_Green_kernel'])
        self.assertFalse(r['gravitational_observation'])

if __name__=='__main__':unittest.main(verbosity=2)
