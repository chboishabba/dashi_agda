#!/usr/bin/env python3
"""Test distinction: Smith '8kV 20A' denotes VA unless real load/phase verified."""
from math import acos,degrees
import unittest
V,I,PIN=8000.,20.,12.
def real_power(power_factor):return V*I*power_factor
def residual(power_factor,losses=0,storage_rate=0):
    return real_power(power_factor)+losses+storage_rate-PIN
class Tests(unittest.TestCase):
 def test_apparent(self):self.assertEqual(V*I,160000)
 def test_resistive(self):self.assertEqual(real_power(1),160000)
 def test_resistive_deficit(self):self.assertEqual(residual(1),159988)
 def test_one_minute(self):self.assertEqual(residual(1)*60,9599280)
 def test_load(self):self.assertEqual(V/I,400)
 def test_tenth_pf(self):self.assertEqual(real_power(.1),16000)
 def test_thousandth_pf(self):self.assertEqual(real_power(.001),160)
 def test_pf_for_12w(self):self.assertEqual(PIN/(V*I),.000075)
 def test_phase_at_12w(self):self.assertAlmostEqual(degrees(acos(PIN/(V*I))),89.9957028165,places=8)
 def test_source_ambiguity(self):self.assertEqual(sum((159988,0,0)),sum((0,159988,0)))
 def test_storage_alternative(self):self.assertEqual(residual(1,storage_rate=-159988),0)
if __name__=='__main__':unittest.main(verbosity=2)
