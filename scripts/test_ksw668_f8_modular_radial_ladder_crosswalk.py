#!/usr/bin/env python3
import unittest
import sympy as s
from ksw668_f8_modular_radial_ladder_crosswalk import (
    r,d,L,J,Jpower,original_radial_ladder,optional_weil_Z3,audit)
class OriginalAdS5ModularSporadicAudit(unittest.TestCase):
 @classmethod
 def setUpClass(cls):cls.x=audit()
 def test_original_even_harmonics(self):self.assertEqual(self.x['physical_even_ell'],[0,2,4])
 def test_not_KK_masses(self):self.assertFalse(self.x['Kaluza_Klein']['spatial_r_radial_spectra_are_KK_mass_spectra'])
 def test_dimension_raise_general(self):
  f=s.Function('f')(r)
  for k in (1,2,4):self.assertEqual(s.simplify(L(d+2*k,Jpower(f,k))-Jpower(L(d,f),k)),0)
 def test_nontrivial_three_channel_ladder(self):self.assertTrue(self.x['radial_ladder']['all_3_channel_interior_shift_commutes'])
 def test_ladder_not_unitary(self):self.assertTrue(self.x['radial_ladder']['noninvertible_J_squared'])
 def test_actual_source_not_generated_by_ladder(self):self.assertTrue(self.x['radial_ladder']['generic_source_not_ladder_related'])
 def test_boundary_not_promoted(self):self.assertFalse(self.x['radial_ladder']['finite_FV_boundary_intertwiner_proved'])
 def test_actual_three_d_reception_not_promoted(self):self.assertFalse(self.x['radial_ladder']['original_sourced_Weyl_receiver_symmetry_proved'])
 def test_Z3_actual_Weil_presentation(self):self.assertTrue(self.x['finite_modular_chart']['S4_I_ST_cubed_equals_S_squared_T3_I_verified'])
 def test_Weil_S_not_PDE_symmetry(self):self.assertFalse(self.x['finite_modular_chart']['modular_S_commutes_with_original_radial_generator'])
 def test_Q_charge_is_not_from_original_physics(self):self.assertFalse(self.x['finite_modular_chart']['chosen_Q_is_physical_AdS5_charge'])
 def test_sporadic_whole_Monster_no_3D_rep(self):self.assertFalse(self.x['Monster']['whole_Monster_nontrivial_3channel_linear_rep_possible'])
 def test_subgroup_C3_is_only_a_chart(self):self.assertTrue(self.x['Monster']['restricted_C3_subgroup_chart_possible'])
 def test_original_F8_numeric_still_open(self):self.assertFalse(self.x['physical_F8_E4_E5_convergence'])
if __name__=='__main__':unittest.main(verbosity=2)
