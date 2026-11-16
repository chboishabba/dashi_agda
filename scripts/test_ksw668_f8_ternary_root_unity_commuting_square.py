#!/usr/bin/env python3
import unittest
from ksw668_f8_ternary_three_harmonic_consumer import verify_fourier_commuting_square_and_zero_sector_no_go
class RootUnityOriginalTTSquare(unittest.TestCase):
 @classmethod
 def setUpClass(cls):cls.res=verify_fourier_commuting_square_and_zero_sector_no_go()
 def test_commuting_square(self):self.assertTrue(self.res['full_three_sector_Fourier_commuting_square_exact'])
 def test_aggregate_zero_character(self):self.assertTrue(self.res['original_receiver_sum_equals_Fourier_trivial_character'])
 def test_zero_sector_not_closed(self):self.assertFalse(self.res['original_trivial_character_sector_dynamically_closed'])
 def test_nontrivial_sector_drives_observable(self):self.assertEqual(self.res['generated_receiver_trivial_character'],-8)
 def test_no_truncation(self):self.assertTrue(self.res['discarding_nontrivial_Fourier_sectors_is_unsound'])
if __name__=='__main__':unittest.main(verbosity=2)
