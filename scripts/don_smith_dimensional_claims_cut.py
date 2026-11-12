#!/usr/bin/env python3
"""Dimensionally source-qualified Smith formula audit; not a physical receipt."""
from dataclasses import dataclass
import unittest
@dataclass(frozen=True)
class D:
 m:int=0; l:int=0; t:int=0; i:int=0
 def __mul__(self,o):return D(self.m+o.m,self.l+o.l,self.t+o.t,self.i+o.i)
 def __truediv__(self,o):return D(self.m-o.m,self.l-o.l,self.t-o.t,self.i-o.i)
 def __pow__(self,n):return D(self.m*n,self.l*n,self.t*n,self.i*n)
V=D(1,2,-3,-1);AMP=D(i=1);FARAD=D(-1,-2,4,2)
HENRY=D(1,2,-2,-2);OHM=D(1,2,-3,-2);TESLA=D(1,0,-2,-1)
HZ=D(t=-1);W=D(1,2,-3);J=D(1,2,-2);SEC=D(t=1)
class Tests(unittest.TestCase):
 def test_v_i_w(self):self.assertEqual(V*AMP,W)
 def test_cap_energy(self):self.assertEqual(FARAD*V**2,J)
 def test_energy_frequency(self):self.assertEqual(FARAD*V**2*HZ,W)
 def test_rc(self):self.assertEqual(OHM*FARAD,SEC)
 def test_lc(self):self.assertEqual(HENRY*FARAD,SEC**2)
 def test_voltage_over_cap_not_hertz(self):self.assertNotEqual(V/FARAD,HZ)
 def test_magnetic_field_not_voltage(self):self.assertNotEqual(TESLA,V)
 def test_voltage_over_resistance_is_current(self):self.assertEqual(V/OHM,AMP)
 def test_sixty_full_cycles(self):self.assertEqual(60,60) # 60Hz already full cycles/s
 def test_smith_fig6_va(self):self.assertEqual(8000*20,160000)
if __name__=='__main__':unittest.main(verbosity=2)
