#!/usr/bin/env python3
import unittest
from ksw668_f8_projected_weyl_sms import algebra
class SMSProjection(unittest.TestCase):
    def test_exact_source_coefficient(self):
        self.assertEqual(algebra()['original_t_4over3_source_coefficient'],'123/20')
    def test_4d_5d_weyl_not_conflated(self):
        self.assertFalse(algebra()['those_two_Weyl_tensors_identical'])
    def test_projected_receiver_not_claimed(self):
        self.assertFalse(algebra()['actual_early_retarded_projected_5D_Weyl_proved'])
    def test_matter_action_open(self):
        self.assertFalse(algebra()['physical_matter_action_generated'])
if __name__=='__main__':unittest.main(verbosity=2)
