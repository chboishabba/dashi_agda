#!/usr/bin/env python3
"""Numerical audit of user-supplied Don Smith 147-page PDF (2022 compilation).
Original claims remain claims; no actual energy gain, wiring or HV test certified.
Runs with local Python stdlib. No CI dependence.
"""
import math, unittest
def storage(c,v): return c*v*v/2
def cap_reactance(c,f): return 1/(2*math.pi*f*c)
def resonant_L(c,f): return 1/((2*math.pi*f)**2*c)
def resistor_power(v,r): return v*v/r
def charge_time_with_bleed(c,v,p,r,n):
    x=n*v*v/(p*r)
    return math.inf if x>=1 else -r*c*math.log1p(-x)/2
def damped_freq(f,c,r):
    q=2*math.pi*f*c*r
    return f*math.sqrt(max(0,1-1/(4*q*q)))
def budget(drive,earth,em,particles,load,loss,storage_change):
    return drive+earth+em+particles-load-loss-storage_change

SOURCE_CASES={
"fig2_5":(10,16,"Smith patent-like plates/dipole"),
"fig6":(17,18,"tabletop board with claimed 160kW output"),
"fig10":(28,28,"1996 suitcase resonant system"),
"fig11":(29,29,"1996 suitcase generator system"),
"fig40":(65,65,"later editor-supplied circuit"),
"chapter4":(67,101,"editor's explicitly unverified practical proposal"),
}
class Audit(unittest.TestCase):
 def test_six_distinct_sources(self):self.assertEqual(len(SOURCE_CASES),6)
 def test_independent_figures(self):self.assertNotEqual(SOURCE_CASES["fig10"],SOURCE_CASES["fig11"])
 def test_output_claim(self):self.assertEqual(8000*20,160000)
 def test_input_claim(self):self.assertEqual(12*1,12)
 def test_ratio_claim(self):self.assertAlmostEqual(160000/12,13333.3333333333)
 def test_unidentified_net_source(self):self.assertEqual(160000-12,159988)
 def test_pdf_nomograph_reactance(self):self.assertAlmostEqual(cap_reactance(100e-9,30000),53.0516476973)
 def test_pdf_nomograph_matching_L(self):self.assertAlmostEqual(resonant_L(100e-9,30000),.0002814477323)
 def test_white_cap(self):self.assertAlmostEqual(storage(3.33e-6,1500),3.74625)
 def test_shunt_1M(self):self.assertEqual(resistor_power(1500,1e6),2.25)
 def test_shunt_2M(self):self.assertEqual(resistor_power(1500,2e6),1.125)
 def test_shunt_4M(self):self.assertEqual(resistor_power(1500,4e6),.5625)
 def test_RC_not_oscillation(self):self.assertAlmostEqual(1/(2*math.pi*1e6*3.33e-6),.0477942772)
 def test_direct_damping_tiny(self):self.assertLess(abs(damped_freq(7800,3.33e-6,1e6)-damped_freq(7800,3.33e-6,2e6)),1e-6)
 def test_shunt_charge_time(self):self.assertGreater(charge_time_with_bleed(3.33e-6,1500,6.7,1e6,1),.559)
 def test_source_world_zero(self):self.assertAlmostEqual(budget(6.7,0,0,0,2,4.7,0),0)
 def test_source_world_nonzero(self):self.assertAlmostEqual(budget(6.7,1,0,0,2,5.7,0),0)
 def test_ideal_reactive_preservation(self):self.assertEqual(storage(3.33e-6,1500),storage(3.33e-6,-1500))
 def test_audio_fraction(self):self.assertAlmostEqual(5/7800,.000641025641025641)
 def test_no_automatic_power_from_cv2f(self):self.assertGreater(storage(3.33e-6,1500)*7800,29000)
if __name__=="__main__":unittest.main(verbosity=2)
