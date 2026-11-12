#!/usr/bin/env python3
"""Finite reciprocal multi-secondary source-energy test. Source-dependent
illustrative values; NOT Smith's claimed physical coil dimensions."""
from math import pi,sqrt
import unittest
F=7800.;W=2*pi*F; Lp=Ls=.001; k=.05; M=k*sqrt(Lp*Ls)
V=15.;Rp=3.;Rs=2.;Rload=100.
def model(n):
    # Tuned resonant primary and secondaries: reflected real impedance.
    zsecondary=Rs+Rload
    zref=n*(W*M)**2/zsecondary
    ip=V/(Rp+zref)
    isec=W*M*ip/zsecondary
    pin=V*ip
    pout=n*isec*isec*Rload
    lossprimary=ip*ip*Rp
    losssecondary=n*isec*isec*Rs
    return dict(n=n,primary_current=ip,each_secondary_current=isec,
       pin=pin,pout=pout,lossprimary=lossprimary,
       losssecondary=losssecondary,reflected_impedance=zref)
class Tests(unittest.TestCase):
 def test_no_load(self):self.assertEqual(model(0)['pout'],0)
 def test_reflection(self):self.assertGreater(model(10)['reflected_impedance'],model(1)['reflected_impedance'])
 def test_primary_load(self):self.assertLess(model(10)['primary_current'],model(1)['primary_current'])
 def test_individual_coupling(self):self.assertLess(model(10)['each_secondary_current'],model(1)['each_secondary_current'])
 def test_conservation(self):
  for n in range(31):
   p=model(n)
   self.assertAlmostEqual(p['pin'],p['pout']+p['lossprimary']+p['losssecondary'],places=9)
 def test_output_below_input(self):
  for n in range(31):self.assertLessEqual(model(n)['pout'],model(n)['pin'])
 def test_one_case(self):self.assertAlmostEqual(model(1)['pout'],1.3878715953)
 def test_ten_case(self):self.assertAlmostEqual(model(10)['pout'],10.0832036954)
 def test_positive_loss(self):self.assertGreater(model(10)['lossprimary'],0)
 def test_more_coupling_reflection(self):self.assertGreater(M,0)
if __name__=='__main__':unittest.main(verbosity=2)
