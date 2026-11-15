#!/usr/bin/env python3
import unittest
from ksw668_f8_null_convex_lens import symbolic,lens,audit
class NullConvexOriginalAdS5(unittest.TestCase):
    def test_exact_positive_null_second_form(self):
        self.assertTrue(symbolic()['strict_null_convex_on_t_1_to_2'])
    def test_original_t2_positive_both_ends(self):
        r=lens()
        self.assertGreater(r['emitter_outward_null_second_form'],0)
        self.assertGreater(r['receiver_outward_null_second_form'],0)
    def test_local_source_and_weyl_symbols_nonzero(self):
        r=lens()
        self.assertGreater(r['product_of_known_local_nonzero_symbol_magnitudes'],0)
        self.assertGreater(r['local_projected_5D_Weyl_principal'],0)
        self.assertLess(r['receiver_normal_symbol'],0)
    def test_dimension_difference(self):
        r=lens()
        self.assertIn('1+4',r['input_null_lens_dimensionality'])
        self.assertIn('1+3',r['Uhlmann_Zhang_2022_original_dimensionality'])
    def test_source_receiver_theorem_fail_closed(self):
        r=lens()
        self.assertFalse(r['actual_5D_Neumann_to_Weyl_composition_proved'])
        self.assertFalse(r['source_to_original_receiver_nonzero_theorem_proved'])
    def test_static_boundary_negative_control(self):
        self.assertFalse(audit()['stationary_control']['strict_convexity'])
if __name__=='__main__':unittest.main(verbosity=2)
