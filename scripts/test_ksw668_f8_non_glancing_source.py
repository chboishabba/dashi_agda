#!/usr/bin/env python3
"""Five microlocal non-promotion controls on exact original t=2 receiver."""
import unittest
from ksw668_f8_non_glancing_source import audit

class MicrolocalPreflight(unittest.TestCase):
    def test_original_exact_receiver(self):
        r=audit()
        self.assertAlmostEqual(r["original_receiver_comoving_r"],.697797781099381,places=12)
        self.assertGreater(r["photon_dark_margin"],.003)
        self.assertTrue(r["strict_inside_bulk_all_chord"])
    def test_real_smooth_source_interior(self):
        r=audit()
        self.assertLess(r["source_x"],r["source_ball_radius"])
        self.assertGreater(r["source_x"],0)
    def test_non_glancing_at_both_ends(self):
        for r in (audit(),audit(6,.024,.0035)):
            self.assertGreater(r["emitter_normal_symbol"],0)
            self.assertLess(r["receiver_normal_symbol"],0)
            self.assertGreater(r["intrinsic_4D_Weyl_principal"],0)
    def test_tiny_support_rejected(self):
        with self.assertRaises(AssertionError):
            audit(2,.00005,.0002)
    def test_no_unproven_transport_promotion(self):
        r=audit()
        self.assertTrue(r["boundary_Poisson_FIO_theorem_application_pending"])
        self.assertFalse(r["actual_nonzero_smooth_compact_source_receiver_theorem_accepted"])
        self.assertFalse(r["physical_graviton_observed"])

if __name__=="__main__":
    unittest.main(verbosity=2)
