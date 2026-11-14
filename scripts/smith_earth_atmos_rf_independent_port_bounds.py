#!/usr/bin/env python3
"""Conditional Maxwell far-field and DC Earth-source bounds: no measured fields."""
from math import pi
import unittest
Z0=376.730313668
def plane_wave_intensity(e_rms):return e_rms*e_rms/Z0
def needed_effective_aperture(w,e_rms,efficiency=1.):
 return w/(efficiency*plane_wave_intensity(e_rms))
def thevenin_max_output(voc,r_internal):
 return voc*voc/(4*r_internal)
def residual_env(pout,pdrive,loss=0,storage_rate=0):
 return pout+loss+storage_rate-pdrive
class Tests(unittest.TestCase):
 def test_field_scaling(self):self.assertAlmostEqual(plane_wave_intensity(2),4*plane_wave_intensity(1))
 def test_1v_rf_smith(self):self.assertGreater(needed_effective_aperture(159988,1),60e6)
 def test_100v_rf_smith(self):self.assertGreater(needed_effective_aperture(159988,100),6000)
 def test_half_eff(self):self.assertAlmostEqual(needed_effective_aperture(100,1,.5),2*needed_effective_aperture(100,1))
 def test_earth_1v10ohm(self):self.assertEqual(thevenin_max_output(1,10),.025)
 def test_earth_48v1000ohm(self):self.assertEqual(thevenin_max_output(48,1000),.576)
 def test_gap(self):self.assertEqual(residual_env(160000,12),159988)
 def test_storage(self):self.assertEqual(residual_env(160000,12,storage_rate=-159988),0)
if __name__=='__main__':unittest.main(verbosity=2)
