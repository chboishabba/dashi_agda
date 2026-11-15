#!/usr/bin/env python3
import unittest
from ksw668_f8_direct_wkb_transport import symbolic,original_receiver
class OriginalDirectWKB(unittest.TestCase):
    def test_exact_null_eikonal_and_5d_tensor_WKB(self):
        self.assertEqual(symbolic()['direct_tensor_WKB_amplitude'],'z^(3/2)')
    def test_next_WKB_transport_cancels_curvature_order_zero(self):
        self.assertTrue(symbolic()['order_lambda_zero_curvature_residual_canceled'])
    def test_direct_ray_transport_nonzero(self):
        self.assertGreater(original_receiver()['direct_ray_transport'],0)
    def test_intrinsic_and_projected_Weyl_nonzero_principal(self):
        r=original_receiver()
        self.assertGreater(r['intrinsic_4D_Weyl_principal_per_lambda'],0)
        self.assertGreater(r['projected_5D_Weyl_principal_per_lambda'],0)
    def test_global_FIO_error_gate_open(self):
        self.assertFalse(original_receiver()['full_5D_Neumann_to_Weyl_FIO_composition_and_error_written'])
    def test_physical_gate_open(self):
        self.assertFalse(original_receiver()['physical_graviton_observed'])
if __name__=='__main__':unittest.main(verbosity=2)
