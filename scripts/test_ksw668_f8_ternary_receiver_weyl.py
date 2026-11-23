#!/usr/bin/env python3
import math,unittest
from ksw668_f8_tt_multipole import propagate
PARAM=dict(dr=.012,dy=.016,dt=.0025,eps=.04,final_t=12.,
           pulse=.065,inside_chord=.012,r_outer=3.15,y_outer=2.6)
class OriginalTernaryReceiverWeyl(unittest.TestCase):
 @classmethod
 def setUpClass(cls):cls.source=propagate(**dict(PARAM,normal_order=3))
 def test_real_original_model(self):self.assertEqual(self.source['model'],'original moving AdS5 a=t Neumann compact TT')
 def test_ternary_canonical_labels(self):self.assertEqual(self.source['unsigned_ternary_mode_digits'],[0,1,2])
 def test_harmonics_not_369_dims(self):self.assertEqual(self.source['effective_radial_dimensions'],[3,7,11])
 def test_source_is_photon_dark(self):self.assertGreater(self.source['discrete_support_photon_margin'],0)
 def test_receiver_H_exact_mode_sum(self):self.assertAlmostEqual(sum(self.source['raw_mode_values']),self.source['retarded_TT_yy_scaled_by_eps4'],places=12)
 def test_receiver_E4_exact_mode_sum(self):self.assertAlmostEqual(sum(self.source['receiver_mode_intrinsic_4D_electric_Weyl']),self.source['receiver_intrinsic_4D_electric_Weyl'],places=12)
 def test_receiver_E5_exact_mode_sum(self):self.assertAlmostEqual(sum(self.source['receiver_mode_projected_5D_electric_Weyl']),self.source['receiver_projected_5D_electric_Weyl'],places=12)
 def test_far_E4_exact_mode_sum(self):self.assertAlmostEqual(sum(self.source['far_mode_intrinsic_4D_electric_Weyl']),self.source['far_intrinsic_4D_electric_Weyl'],places=12)
 def test_far_E5_exact_mode_sum(self):self.assertAlmostEqual(sum(self.source['far_mode_projected_5D_electric_Weyl']),self.source['far_projected_5D_electric_Weyl'],places=12)
 def test_attributions_nontrivial(self):self.assertTrue(any(abs(x)>1e-15 for x in self.source['receiver_mode_intrinsic_4D_electric_Weyl']))
 def test_all_component_values_finite(self):
  for k in ('receiver_mode_intrinsic_4D_electric_Weyl','receiver_mode_projected_5D_electric_Weyl'):
   self.assertTrue(all(math.isfinite(x) for x in self.source[k]))
 def test_no_C3_pde_promotion(self):self.assertTrue(self.source['unsigned_ternary_codec_not_physical_C3_action'])
 def test_corrected_provenance(self):self.assertEqual(self.source['intrinsic_4D_weyl_spatial_operator'],'full_reconstructed_Delta3')
 def test_legacy_spatial_difference(self):
  r=self.source
  for j in range(3):
   self.assertAlmostEqual(r['receiver_mode_intrinsic_4D_electric_Weyl'][j]-r['receiver_mode_intrinsic_4D_electric_Weyl_legacy_axial'][j],(r['receiver_mode_Hxx'][j]-r['receiver_mode_Delta3H'][j])/(4*r['receiver_t']**2),places=10)
 def test_both_weyl_uncertified(self):self.assertFalse(self.source['full_Weyl_receiver_certified'])
if __name__=='__main__':unittest.main(verbosity=2)
