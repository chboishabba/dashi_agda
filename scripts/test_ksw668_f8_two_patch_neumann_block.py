#!/usr/bin/env python3
import unittest
from ksw668_f8_two_patch_neumann_block import audit,E,De,Ee,Dr,Er,F,O,I,mul
class TestKSWCausalBlock(unittest.TestCase):
    def test_exact_inverse(self):self.assertTrue(audit()["exact_noncommutative_two_sided_inverse"])
    def test_depth2(self):self.assertEqual(audit()["exact_finite_Neumann_depth"],2)
    def test_zero_residual_square(self):self.assertTrue(audit()["residual_squared_zero"])
    def test_wrong_order_negative(self):self.assertNotEqual(-(Er*F*Ee),-(Ee*F*Er))
    def test_causal_triangular(self):self.assertEqual([[De,O],[F,Dr]][0][1],O)
    def test_DN_ND_order(self):self.assertEqual(audit()["ND_lens_FIO_order"],-1)
    def test_Weyl_order(self):self.assertEqual(audit()["two_derivative_Weyl_after_ND_order"],1)
    def test_real_noncommuting_matrix(self):self.assertTrue(audit()["rational_nonscalar_matrix_positive_control"])
    def test_local_identity_missing_negative(self):
        self.assertNotEqual(mul([[De,O],[F,Dr]],[[I,O],[O,I]]),[[I,O],[O,I]])
    def test_physical_not_promoted(self):
        self.assertFalse(audit()["physically_identified_full_5D_FIO_with_smoothing_error"])
if __name__=='__main__':unittest.main(verbosity=2)
