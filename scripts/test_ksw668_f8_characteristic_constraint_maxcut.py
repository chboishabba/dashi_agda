#!/usr/bin/env python3
import unittest
import numpy as np
from ksw668_f8_characteristic_constraint_maxcut import (
    compare,actual_stage,normal_commutator_certificate,
    rk3_constraint_step,smooth_drift,forced_source_lift,audit,
    D_y,D_w,physical_constraint)
from ksw668_f8_full_coupled_weighted_sbp_energy import setup,coeff
class OriginalPhysicalCharacteristicConstraint(unittest.TestCase):
 @classmethod
 def setUpClass(cls):cls.data=audit()
 def test_actual_original_slices(self):self.assertEqual([x['t'] for x in self.data['measured_original_slices']],[1.,4/3,2.,12.])
 def test_mode3_exact_constraint_interior(self):
  self.assertTrue(all(x['unweighted_mode3_interior_Cdot']<1e-9 for x in self.data['measured_original_slices']))
 def test_mode4_has_defect_for_rough_finite_state(self):
  self.assertTrue(all(x['weighted_mode4_interior_Cdot']>.1 for x in self.data['measured_original_slices']))
 def test_exact_energy_commutator_identity(self):
  self.assertTrue(all(abs(x['weighted_commutator_identity_residual'])<1e-9 for x in self.data['measured_original_slices']))
 def test_original_SSPRK3_three_stages_preserve_mode3_interior(self):
  self.assertLess(self.data['actual_RK3_stage_constraint_test'][3]['interior'],1e-10)
 def test_weighted_mode4_SSPRK3_nonzero_constraint_defect(self):
  self.assertGreater(self.data['actual_RK3_stage_constraint_test'][4]['interior'],1e-5)
 def test_boundary_SAT_not_closed_by_interior_identity(self):
  self.assertGreater(self.data['actual_RK3_stage_constraint_test'][3]['boundary'],1e-4)
 def test_smooth_second_order_difference(self):
  a=self.data['smooth_weighted_constraint_defect']
  self.assertTrue(all(a[i]/a[i+1]>3.7 for i in range(3)))
 def test_commutator_Gershgorin_4_over_b_all_original_slices(self):
  self.assertEqual(len(self.data['explicit_normal_commutator_Gershgorin_certificates']),16)
  for x in self.data['explicit_normal_commutator_Gershgorin_certificates']:
   self.assertLessEqual(x['Gershgorin_bound'],x['proven_analytic_uniform_bound']+1e-8)
 def test_original_t12_weighted_energy_bound(self):
  x=normal_commutator_certificate(12,13,1/48)
  self.assertAlmostEqual(x['mode3_coupled_Eprime_over_E_bound'],197)
 def test_reject_out_of_scope_normal_mesh(self):
  with self.assertRaises(ValueError):normal_commutator_certificate(12,13,1/12)
 def test_coupled_homogeneous_bound_mode3(self):
  for t in (1.,4/3,2.,12.):
   x=compare(t=t,ny=15,nr=7,dy=1/(10*t),dr=.02,seed=37)
   self.assertLessEqual(x['Eprime_mode3'],(5+16*t)*x['E']+1e-9)
 def test_actual_stage_not_decorative(self):
  x=setup(t=4/3,ny=9,nr=6)
  self.assertGreater(float(np.linalg.norm(actual_stage(x,3)[1])),0)
 def test_forced_lift_all_original_slices(self):
  self.assertEqual(len(self.data['full_coupled_original_sourced_lift_checks']),4)
  for x in self.data['full_coupled_original_sourced_lift_checks']:
   self.assertTrue(x['sourced_coupled_semidiscrete_energy_and_constraint_closed'])
 def test_sourced_lift_exact_stage_residual(self):
  self.assertTrue(all(x['source_lift_operator_error']<1e-9 for x in self.data['full_coupled_original_sourced_lift_checks']))
 def test_sourced_interior_constraint(self):
  self.assertTrue(all(x['interior_constraint_Cdot']<1e-9 for x in self.data['full_coupled_original_sourced_lift_checks']))
 def test_original_compact_TT_four_time_slices(self):
  x=self.data['actual_original_compact_3D_TT_sourced_lift_checks']
  self.assertEqual([r['t'] for r in x],[1.,4/3,2.,12.])
  self.assertTrue(all(r['original_compact_3D_TT_source'] for r in x))
 def test_actual_compact_TT_source_lift_residual(self):
  self.assertTrue(all(r['source_lift_operator_error']<1e-9
    for r in self.data['actual_original_compact_3D_TT_sourced_lift_checks']))
 def test_actual_compact_TT_interior_physical_constraint(self):
  self.assertTrue(all(r['interior_constraint_Cdot']<1e-9
    for r in self.data['actual_original_compact_3D_TT_sourced_lift_checks']))
 def test_actual_compact_TT_no_fictitious_Weyl_closure(self):
  x=self.data['actual_original_compact_3D_TT_sourced_lift_checks']
  self.assertTrue(all(r['original_compact_3D_TT_source'] and
    r['energy_derivative']<=r['forced_energy_bound'] for r in x))
  self.assertTrue(self.data['both_Weyl_curvature_convergence_accepted']==False)
 def test_sourced_energy_includes_radial_force(self):
  x=forced_source_lift(t=12.)
  self.assertLessEqual(x['energy_derivative'],x['forced_energy_bound'])
 def test_exact_physical_D_not_weighted_D(self):
  x=setup(t=4/3,ny=9,nr=7)
  self.assertGreater(float(np.linalg.norm(D_y(x['P'],x['dy'])-D_w(x['P'],x['z'],x['dy']))),.1)
 def test_global_weak_boundary_not_promoted(self):
  self.assertFalse(self.data['global_weak_Israel_constraint_weld_accepted'])
 def test_no_explicit_full_RK3_or_both_Weyl_promotion(self):
  self.assertFalse(self.data['full_explicit_RK3_coupled_energy_accepted'])
  self.assertFalse(self.data['both_Weyl_curvature_convergence_accepted'])
if __name__=='__main__':unittest.main(verbosity=2)
