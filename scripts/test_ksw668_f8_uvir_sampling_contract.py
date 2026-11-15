#!/usr/bin/env python3
import unittest
from ksw668_f8_uvir_sampling_contract import grid,design,audit
class SamplingContract(unittest.TestCase):
 def test_axes(self):self.assertTrue(audit()['independent_UV_cutoff_and_IR_spacing_axes'])
 def test_current_phase(self):self.assertGreater(grid()['large_kr_bessel_sample_phase_increment'],2.8)
 def test_Nx_fixed_dk(self):self.assertAlmostEqual(grid(768)['dk'],grid(3072)['dk'])
 def test_Nx_kmax_doubles(self):self.assertAlmostEqual(grid(1536)['kmax'],2*grid(768)['kmax'])
 def test_L_spacing_half(self):self.assertAlmostEqual(grid(L=8)['dk'],.5*grid(L=4)['dk'])
 def test_L_fixedN_uv_worsens(self):self.assertLess(grid(L=8)['u_max'],grid(L=4)['u_max'])
 def test_uniform_N(self):self.assertGreater(design()['minimum_even_Nx_in_this_uniform_design'],60000)
 def test_target_u(self):self.assertGreaterEqual(design()['corresponding_grid']['u_max'],100)
 def test_target_phase(self):self.assertAlmostEqual(design()['corresponding_grid']['large_kr_bessel_sample_phase_increment'],.25)
 def test_not_universal(self):self.assertTrue(design()['not_a_universal_numerical_lower_bound'])
 def test_invalid(self):
  with self.assertRaises(ValueError):grid(L=-1)
 def test_not_physical(self):self.assertFalse(audit()['original_a_t_receiver_weyl_accepted'])
if __name__=='__main__':unittest.main(verbosity=2)
