#!/usr/bin/env python3
import unittest
from ksw668_f8_original_energy_weyl_trace_no_go import symbolic,audit
class OriginalWeylTraceNoGo(unittest.TestCase):
 def test_exact_five_dimensional_bulk_wave(self):self.assertEqual(symbolic()['exact_bulk_wave_residual'],'0')
 def test_actual_moving_normal(self):self.assertIn('H_T',symbolic()['original_Israel_G'])
 def test_intrinsic_original_t2_coefficient(self):self.assertEqual(symbolic()['original_t2_E4_peak'],'9*N/64')
 def test_bounded_H1(self):self.assertEqual(len({x['weighted_H1_energy'] for x in audit()['samples']}),1)
 def test_unbounded_Weyl(self):
  a=audit()['samples'];self.assertEqual(a[-1]['intrinsic_4D_Weyl_at_t2'],2*a[-2]['intrinsic_4D_Weyl_at_t2'])
 def test_original_geometry(self):self.assertTrue(audit()['same_original_a_equals_t_model'])
 def test_higher_sobolev_needed(self):self.assertTrue(audit()['source_to_receiver_higher_Sobolev_trace_bound_needed'])
 def test_periodic_not_compact(self):self.assertTrue(symbolic()['periodic_3torus_not_compact_R3'])
 def test_not_compact_source_counterexample(self):self.assertFalse(symbolic()['compact_source_FIO_theorem_refuted'])
 def test_experiment_open(self):self.assertFalse(audit()['experimental_graviton_observed'])
if __name__=='__main__':unittest.main(verbosity=2)
