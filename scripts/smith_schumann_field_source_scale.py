#!/usr/bin/env python3
"""Conditional measured-Schumann-to-receiver scale model.
Travelling-wave equivalent intensity is ONLY a comparison, not a net
Poynting flux claim for a standing Earth-ionosphere resonance.
"""
from math import pi
import unittest
Z0=376.730313668; F=7.83; GAP=159988.; E=.0003; B=1e-12
EARTH_AREA=4*pi*6371000**2
def plane_proxy(e):return e*e/Z0
def ideal_aperture(p,e):return p/plane_proxy(e)
def magnetic_emf(n,area,b=B):return 2*pi*F*n*area*b
class Tests(unittest.TestCase):
 def test_gap(self):self.assertEqual(160000-12,GAP)
 def test_historical_other_scale(self):self.assertAlmostEqual(.5*3.33e-6*1500**2*7800,29220.75)
 def test_one_volt_field_area(self):self.assertAlmostEqual(ideal_aperture(GAP,1),60272329.4231,delta=1)
 def test_earth_sized_area_proxy(self):self.assertGreater(ideal_aperture(GAP,E)/EARTH_AREA,1)
 def test_emf(self):self.assertAlmostEqual(magnetic_emf(100,1),4.9197341e-9)
 def test_e_sensitivity(self):self.assertAlmostEqual(ideal_aperture(GAP,E*2),ideal_aperture(GAP,E)/4)
 def test_magnetic_scaling(self):self.assertAlmostEqual(magnetic_emf(200,1),2*magnetic_emf(100,1))
 def test_standing_wave_warning(self):self.assertGreater(plane_proxy(E),0) # not net measured flux
if __name__=="__main__":unittest.main(verbosity=2)
