#!/usr/bin/env python3
"""Source-bounded reflected load vs radiative reflection. Python stdlib only.
Companion: local full 2-mode/open-Maxwell 30-test package.
No Smith/Filsinger hardware or atmospheric harvest is claimed proven.
"""
from math import pi,sqrt,isclose
import unittest
def reflection_and_extraction(ge,gi,gl):
    den=(ge+gi+gl)**2
    return dict(reflected=(ge-gi-gl)**2/den,
                useful=4*ge*gl/den,
                heat=4*ge*gi/den)
def reflected_secondary_impedance(n,f,lp,ls,k,rs,rload):
    m=k*sqrt(lp*ls)
    return n*(2*pi*f*m)**2/(rs+rload)
def radiation_resistance_hertzian(length,wavelength,z0=376.730313668):
    # Uniform-current electrically short dipole, radiation zone
    return 2*pi*z0/3*(length/wavelength)**2
class Tests(unittest.TestCase):
 def test_critical_reflection(self):
    x=reflection_and_extraction(.04,.02,.02)
    self.assertAlmostEqual(x['reflected'],0)
    self.assertAlmostEqual(x['useful'],.5)
 def test_max_useful_differs(self):
    x=reflection_and_extraction(.04,.02,.06)
    self.assertAlmostEqual(x['reflected'],1/9)
    self.assertAlmostEqual(x['useful'],2/3)
 def test_energy_conservation(self):
    for load in (.001,.02,.04,.06,.4):
     self.assertAlmostEqual(sum(reflection_and_extraction(.04,.02,load).values()),1)
 def test_secondary_reflection(self):
    f=lambda n:reflected_secondary_impedance(n,7800,.001,.001,.05,2,100)
    self.assertAlmostEqual(f(10),10*f(1))
 def test_open_dipole_radiation(self):
    self.assertGreater(radiation_resistance_hertzian(1,300),0)
    self.assertAlmostEqual(radiation_resistance_hertzian(2,300),4*radiation_resistance_hertzian(1,300))
 def test_no_gain_assertion(self):
    self.assertLessEqual(reflection_and_extraction(.04,.02,.06)['useful'],1)
if __name__=='__main__':unittest.main(verbosity=2)
