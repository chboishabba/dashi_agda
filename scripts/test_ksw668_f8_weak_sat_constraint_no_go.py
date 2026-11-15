#!/usr/bin/env python3
import unittest
from ksw668_f8_weak_sat_constraint_no_go import witness,audit
class WeakSATGlobalConstraintNegativeControl(unittest.TestCase):
 def test_original_exact_rational_t43(self):self.assertAlmostEqual(witness()['exact_wall_constraint_rate'],20.)
 def test_three_normal_spacing_scaling(self):self.assertEqual([r['exact_wall_constraint_rate'] for r in audit()['rows']],[10.,20.,40.])
 def test_initially_constrained(self):self.assertTrue(witness()['original_initial_physical_constraint_exact_zero'])
 def test_interior_still_preserved(self):self.assertEqual(witness()['exact_interior_constraint_rate'],0)
 def test_global_wall_not_closed(self):self.assertFalse(witness()['global_constraint_preservation_closed'])
 def test_outside_original_time_rejected(self):
  with self.assertRaises(ValueError):witness(t=.5)
if __name__=='__main__':unittest.main(verbosity=2)
