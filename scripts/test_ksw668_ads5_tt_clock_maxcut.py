#!/usr/bin/env python3
"""Nine local non-promotion regression gates for KSW AdS5/clock continuation."""
import unittest
import ksw668_ads5_tt_clock_maxcut as a

class TestOriginalObjectMaxCut(unittest.TestCase):
    def test_A4_rigidity(self):
        r=a.cylindrical_flat_bulk_rigidity()
        self.assertFalse(r['nonstatic_Rtau_allowed_with_fixed_T_f_n'])
        self.assertFalse(r['full_braneworld_linear_stability_proved'])
    def test_B2_compact_TT_transverse_trace(self):
        r=a.tt_source()
        self.assertTrue(r['background_FRW_covariant_divergence_zero'])
        self.assertEqual((r['initial_local_x4_yy_value'],r['initial_local_x4_zz_value']),(24,-24))
    def test_B2_microphysical_premise_not_paid(self):
        self.assertFalse(a.tt_source()['physical_matter_action_derived'])
    def test_B3_boundary_timelike(self):
        r=a.moving_boundary()
        self.assertTrue(r['strictly_timelike'])
        self.assertEqual(r['uniform_y_coefficient_lower'],'1/2')
    def test_B3_energy_not_sign_definite(self):
        r=a.moving_boundary()
        self.assertTrue(r['flux_can_have_either_sign'])
        self.assertFalse(r['Green_operator_wellposedness_from_this_alone'])
    def test_B5_static_packet(self):
        r=a.static_finite_energy_packet()
        self.assertTrue(r['finite_total_energy_for_f_TT_H1'])
        self.assertFalse(r['moving_neumann_supported'])
    def test_C1_cubic_law(self):
        r=a.short_baseline()
        self.assertAlmostEqual(r['exact_numeric_eps_delta_ratio'][-1][-1],1,delta=.002)
        self.assertTrue(r['rescaling_alone_does_not_solve_C1'])
    def test_clock_reference_lapse_invariance(self):
        r=a.clock_gauge_invariance()
        self.assertTrue(r['lapse_reparametrization_does_not_change_proper_time'])
        self.assertGreater(r['same_receiver_proper_time_advance'],r['same_receiver_conformal_time_excess'])
    def test_no_empirical_promotion(self):
        r=a.audit()
        self.assertFalse(r['physical_retarded_graviton'])
        self.assertFalse(r['agda_kernel_accepted'])

if __name__=='__main__':
    unittest.main(verbosity=2)
