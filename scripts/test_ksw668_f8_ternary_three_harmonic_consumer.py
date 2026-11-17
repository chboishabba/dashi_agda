#!/usr/bin/env python3
import unittest
import sympy as sp
from ksw668_f8_ternary_three_harmonic_consumer import (
 DIGITS,ELL,DIMS,even_ell,digit_for_ell,radial_dimension,legendre_components,
 physical_tt_angular_symbol,receiver_yy_from_radial_V,verify_angular_exact,
 verify_c3_non_intertwining,actual_original_angular_source_profiles,audit)
class TernaryTTConsumer(unittest.TestCase):
 def test_base369_unsigned_digits(self):self.assertEqual(DIGITS,(0,1,2))
 def test_exact_bidi(self):self.assertTrue(all(digit_for_ell(even_ell(q))==q for q in DIGITS))
 def test_ell_labels(self):self.assertEqual(tuple(map(even_ell,DIGITS)),ELL)
 def test_effective_radial_dimensions_not_369(self):self.assertEqual(tuple(map(radial_dimension,DIGITS)),DIMS)
 def test_reject_nonphysical_label(self):
  with self.assertRaises(ValueError):digit_for_ell(6)
 def test_reject_bad_unsigned(self):
  with self.assertRaises(ValueError):even_ell(3)
 def test_no_bool_as_digit(self):
  with self.assertRaises(ValueError):even_ell(True)
 def test_exact_legendre(self):self.assertTrue(verify_angular_exact()['three_channel_angular_reconstruction_exact'])
 def test_finite_sample_symbol(self):
  for mu in [-1,0,sp.Rational(1,3),1]:
   self.assertEqual(sp.simplify(sum(legendre_components(mu))-physical_tt_angular_symbol(mu)),0)
 def test_receiver_axis_weights(self):self.assertEqual(sum(legendre_components(1)),1)
 def test_radii_vary_mode_factors(self):
  self.assertEqual(receiver_yy_from_radial_V([1,1,1],2,1),21)
 def test_invalid_receiver(self):
  with self.assertRaises(ValueError):receiver_yy_from_radial_V([1,1],2,1)
 def test_angular_laplacian_weld(self):self.assertTrue(verify_angular_exact()['radial_angular_laplacian_weld_exact'])
 def test_counterexample_C3_cycle(self):self.assertEqual(verify_c3_non_intertwining()['explicit_cycle_commutator_witness'],8)
 def test_C3_not_dynamics(self):self.assertFalse(verify_c3_non_intertwining()['C3_label_cycle_commutes_with_original_radial_operator'])
 def test_omega_Fourier_is_lossless(self):self.assertTrue(verify_c3_non_intertwining()['C3_fourier_unitary_bidi'])
 def test_omega_Fourier_does_not_diagonalize_PDE(self):self.assertFalse(verify_c3_non_intertwining()['Fourier_basis_preserves_original_uncoupled_radial_channels'])
 def test_actual_original_source_consumer(self):self.assertEqual(actual_original_angular_source_profiles()['actual_producer_ell'],[0,2,4])
 def test_not_both_weyl_closure(self):self.assertFalse(audit()['original_photon_dark_and_both_Weyl_convergence'])
 def test_not_5D_symmetry(self):self.assertFalse(audit()['original_C3_dynamical_symmetry_claimed'])
if __name__=='__main__':unittest.main(verbosity=2)
