#!/usr/bin/env python3
"""Local-only original-vs-test-brane tests. No external physical data fabricated."""
import math
import unittest
import ksw668_brane_bulk_shortcut_same_metric as Geometry
import ksw668_brane_winding_stability_source as Worldvolume
import ksw668_compact_kk_mode_dispersion as ProductKK

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

    def test_KK_mass_tower_is_not_a_shortcut(self):
        report=ProductKK.audit()
        self.assertAlmostEqual(report["n1_R1_k3_group_velocity"],3/math.sqrt(10))
        self.assertLess(report["n1_R1_k3_group_velocity"],1)
        self.assertFalse(report["product_compact_KK_alone_shortcut"])
        self.assertFalse(report["curved_brane_shortcut_excluded"])
        self.assertFalse(report["SUSY_or_string_identification_proven"])

if __name__=="__main__":
    unittest.main(verbosity=2)
