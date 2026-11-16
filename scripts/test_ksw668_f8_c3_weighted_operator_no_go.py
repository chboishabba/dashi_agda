import unittest
import numpy as np
from ksw668_f8_c3_weighted_operator_no_go import audit,normalized_radial
class OriginalActualRadialC3NoGo(unittest.TestCase):
 def test_unitary_after_native_volume_norm(self):self.assertTrue(audit()['compensated_C3_is_unitary'])
 def test_cube_identity(self):self.assertTrue(audit()['compensated_C3_cube_is_identity'])
 def test_nonzero_full_matrix_commutator(self):self.assertGreater(audit()['full_operator_C3_commutator_Frobenius'],1)
 def test_radial_spectra_different(self):self.assertTrue(all(x>0 for x in audit()['eigenvalue_gaps_vs_ell0']))
 def test_nonintertwiner_after_weight_compensation(self):self.assertFalse(audit()['radial_channel_C3_is_physical_symmetry'])
 def test_three_meshes(self):
  for n,dr in ((5,.04),(9,.018),(15,.01)):
   self.assertGreater(audit(n,dr)['full_operator_C3_commutator_Frobenius'],1)
 def test_selfadjoint_each_mode(self):
  for d in (3,7,11):
   S,V,L=normalized_radial(d,12,.015)
   self.assertTrue(np.allclose(S,S.T,atol=1e-9))
 def test_only_natural_cycle_no_go(self):self.assertFalse(audit()['arbitrary_nonlocal_intertwiners_all_disproved'])
if __name__=='__main__':unittest.main()
