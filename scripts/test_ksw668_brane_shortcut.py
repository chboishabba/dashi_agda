#!/usr/bin/env python3
"""Local-only original-vs-test-brane tests. No external physical data fabricated."""
import math
import unittest
import ksw668_brane_bulk_shortcut_same_metric as Geometry
import ksw668_brane_winding_stability_source as Worldvolume
import ksw668_compact_kk_mode_dispersion as ProductKK
import ksw668_caldwell_langlois_original_eq19 as OriginalAdS
import ksw668_caldwell_langlois_israel_exact as Israel
import ksw668_brane_scalar_emitter_receiver_retarded as ScalarReceiver
import ksw668_ads5_tensor_mode_moving_israel_bc as TensorBC
import ksw668_ads5_gravitational_horizon_variance_bound as StrictHorizon

class BraneMaxCutTests(unittest.TestCase):
    def test_actual_same_ambient_metric_and_apparent_shortcut(self):
        report=Geometry.audit()
        self.assertEqual(report["induced_4D_metric"],"diag(-1,R^2,1,1)")
        self.assertTrue(report["5D_bulk_null_straight_geodesic"])
        self.assertTrue(report["4D_brane_confined_intrinsically_null_curve"])
        self.assertEqual(report["bulk_arrival_time_in_units_R"],2)
        self.assertAlmostEqual(report["brane_light_arrival_time_in_units_R"],math.pi)
        self.assertGreater(report["induced_interval_squared_at_early_arrival_units_R2"],0)
        self.assertTrue(report["5D_global_causality_not_violated"])
        self.assertFalse(report["physical_FTL_or_closed_timelike_curve"])

    def test_not_dynamical_or_operational(self):
        report=Geometry.audit()
        self.assertEqual(report["cylindrical_extrinsic_trace"],"-1/R")
        self.assertFalse(report["tension_only_brane_stationary"])
        self.assertFalse(report["5D_Einstein_with_brane_backreaction_solved"])
        self.assertFalse(report["bulk_excitation_source_detector_coupling"])
        self.assertFalse(report["independent_gravitational_signal_measured"])

    def test_static_warp_no_shortcut(self):
        report=Geometry.audit()
        self.assertFalse(report["static_warp_same_time_space_bulk_shortcut"])
        self.assertGreater(report["static_warp_detour_time"],
                           report["static_warp_onbrane_time"])

    def test_positive_energy_winding_stabilisation(self):
        report=Worldvolume.audit()
        self.assertEqual(report["example_T2_f2_n1_radius"],1)
        self.assertTrue(report["uniform_radial_stable"])
        self.assertEqual(report["example_min_energy_per_uv_area"],"8*pi")
        self.assertEqual(report["bulk_massless_scalar_pulse_equation"],
                         "PASS; F(t+X) exact solution")
        self.assertFalse(report["5D_gravitating_Einstein_Israel_solution"])
        self.assertFalse(report["localized_source_receiver_coupling"])
        self.assertFalse(report["real_free_energy_or_superluminal"])

    def test_caldwell_langlois_original_AdS5_metric_and_FRW(self):
        r=OriginalAdS.audit()
        self.assertEqual(r["original_paper_DOI"],"10.1016/S0370-2693(01)00631-1")
        self.assertEqual(r["bulk_Ricci_scalar"],"-20")
        self.assertTrue(r["bulk_Einstein_Lambda_all_25"])
        self.assertTrue(r["original_Friedmann_and_continuity"])
        self.assertTrue(r["brane_rho_plus_pressure_positive"])
        self.assertTrue(r["original_bulk_null_and_geodesic"])
        self.assertFalse(r["all_Israel_distributional_conditions_independently_accepted"])

    def test_original_AdS5_Z2_Israel_full_spacetime_junction(self):
        r=Israel.audit()
        self.assertEqual(r["original_paper_DOI"],"10.1016/S0370-2693(01)00631-1")
        self.assertEqual(r["geometric_K_mixed_t"],"-1/sqrt(1+t^-2)")
        self.assertEqual(r["geometric_K_mixed_i"],"-sqrt(1+t^-2)")
        self.assertTrue(r["unit_normal_and_induced_clock"])
        self.assertTrue(r["classical_Z2_Israel_all_16"])
        self.assertTrue(r["rho_plus_p_positive"])
        self.assertFalse(r["bulk_linearised_graviton_and_stability_proved"])
        self.assertFalse(r["physical_bulk_source_detector_response"])

    def test_same_receiver_original_gravitational_horizon_arrives_earlier(self):
        r=OriginalAdS.audit()
        self.assertAlmostEqual(r["photon_horizon_at_t2"],math.log(2),places=12)
        self.assertAlmostEqual(r["bulk_horizon_at_t2"],.697797781099381,places=9)
        self.assertGreater(r["same_receiver_comoving_r"],r["photon_horizon_at_t2"])
        self.assertAlmostEqual(r["same_receiver_photon_proper_t"],2.009322862731128,places=9)
        self.assertAlmostEqual(r["same_receiver_bulk_time_advantage"],.009322862731128,places=9)
        self.assertFalse(r["bulk_graviton_emission_detection"])
        self.assertFalse(r["FTL_in_full5D_or_CTC"])

    def test_KK_mass_tower_is_not_a_shortcut(self):
        report=ProductKK.audit()
        self.assertAlmostEqual(report["n1_R1_k3_group_velocity"],3/math.sqrt(10))
        self.assertLess(report["n1_R1_k3_group_velocity"],1)
        self.assertFalse(report["product_compact_KK_alone_shortcut"])
        self.assertFalse(report["curved_brane_shortcut_excluded"])
        self.assertFalse(report["SUSY_or_string_identification_proven"])


    def test_actual_localized_test_scalar_earlier_same_receiver_response(self):
        r=ScalarReceiver.audit()
        self.assertTrue(r["retarded_no_signal_before_ambient_null_front"])
        self.assertTrue(r["signal_prior_to_brane_light"])
        self.assertGreater(r["receiver_response_at_t"],0)
        self.assertLess(r["same_receiver_earlier_test_t"],
                        r["brane_restricted_photon_first_front_t"])
        self.assertFalse(r["ideal_point_source_total_energy_finite"])
        self.assertFalse(r["bulk_field_is_real_graviton"])
        self.assertFalse(r["observed_experiment"])

    def test_bulk_scalar_first_front_causality_and_wrong_inputs(self):
        for t in (-1.,0.,1.999999,2.):
            self.assertEqual(
               ScalarReceiver.retarded_receiver(t,2.,.25),0.)
        self.assertGreater(
            ScalarReceiver.retarded_receiver(2.125,2.,.25),0.)
        for args in ((2.1,0.,.1),(2.1,2.,0.),(2.1,2.,-.01)):
            with self.assertRaises(ValueError):
                ScalarReceiver.retarded_receiver(*args)
        with self.assertRaises(ValueError):
            ScalarReceiver.audit(1.,3.)

    def test_exact_source_rational_receiver_slice(self):
        # Polygonal source path: chord d=6, brane length=10,
        # t=15/2, tau=2. Only first causal radical contributes.
        r=ScalarReceiver.retarded_receiver(7.5,6.,2.)
        self.assertAlmostEqual(4*math.pi**2*r,1./8.,places=12)
        self.assertTrue(6<7.5<10)

    def test_original_ads5_TT_bulk_mode_does_not_satisfy_moving_israel_BC(self):
        r=TensorBC.audit()
        self.assertTrue(r["bulk_TT_PDE_all_xTz_exact"])
        self.assertTrue(r["normal_unit_spacelike"])
        self.assertTrue(r["normal_tangent_orthogonal"])
        self.assertGreater(r["one_separated_mode_residual_numeric"],.6)
        self.assertFalse(r["one_separated_mode_solves_full_moving_BC"])
        self.assertTrue(r["homogeneous_constant_mode_solves_moving_BC"])
        self.assertFalse(r["physical_graviton_source_receiver_or_measured_effect"])

    def test_original_ads5_cosmology_strict_variance_lower_bound(self):
        r=StrictHorizon.audit()
        self.assertGreater(r["same_interval_horizon_excess"],0)
        self.assertGreater(r["proven_variance_lower_bound_on_horizon_excess"],0)
        self.assertLessEqual(r["proven_variance_lower_bound_on_horizon_excess"],
                             r["same_interval_horizon_excess"])
        self.assertEqual(r["finite_positive_weight_variants_tested"],280)
        self.assertTrue(r["constant_H_no_shortcut_control"])
        self.assertFalse(r["analytic_Agda_continuum_sqrt_integration_kernel_accepted"])

if __name__=="__main__":
    unittest.main(verbosity=2)
