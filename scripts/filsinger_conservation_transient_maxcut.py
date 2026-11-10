#!/usr/bin/env python3
"""Conservation-only transient charging bounds for Filsinger candidate.
Independent of unknown electrical topology and acoustic switching frequency.
No claim of verified 6.7 W input, zero initial charge or Earth harvesting.
"""
from math import sqrt
import unittest
C = 3.33e-6  # F, narrated
P = 6.7      # W, reported, only conditionally treated as real source input
V = 1500.0   # V, narrated target
C_BLUE = 2e-6 # F, visually tentative only

def energy(c,v):return c*v*v/2
def minimum_time(c,v,p,eff=1.0):return energy(c,v)/(p*eff)
def max_voltage_at(c,t,p,eff=1.0):return sqrt(2*p*eff*t/c)
def unexplained_energy_if_initially_empty(c,v,t,p,eff=1.0):
    """Unmet energy, not automatically Earth energy; precharge/other source possible."""
    return max(0.0,energy(c,v)-p*t*eff)

class ConservationTests(unittest.TestCase):
    def test_energy(self):self.assertAlmostEqual(energy(C,V),3.74625)
    def test_ideal_charge_time(self):self.assertAlmostEqual(minimum_time(C,V,P),.559141791044776)
    def test_half_eff_charge_time(self):self.assertAlmostEqual(minimum_time(C,V,P,.5),1.118283582089552)
    def test_300ms_max_voltage(self):self.assertAlmostEqual(max_voltage_at(C,.3,P),1098.729,delta=.01)
    def test_300ms_source_deficit(self):self.assertAlmostEqual(unexplained_energy_if_initially_empty(C,V,.3,P),1.73625)
    def test_300ms_ideal_required_power(self):self.assertAlmostEqual(energy(C,V)/.3,12.4875)
    def test_300ms_insufficient(self):self.assertLess(max_voltage_at(C,.3,P),V)
    def test_half_second_insufficient(self):self.assertLess(max_voltage_at(C,.5,P),V)
    def test_one_second_sufficient_ideal(self):self.assertGreater(max_voltage_at(C,1.,P),V)
    def test_two_bank_ideal_time(self):
        self.assertAlmostEqual((energy(C,V)+energy(C_BLUE,V))/P,.8949626865671642)
    def test_blue_10kV_energy_tentative(self):self.assertAlmostEqual(energy(C_BLUE,10000),100)
    def test_full_reset_would_be_large_power(self):self.assertAlmostEqual(energy(C,V)*7800,29220.75)
    def test_reactive_sign_flip_keeps_energy(self):self.assertEqual(energy(C,V),energy(C,-V))
    def test_environment_unidentified_worlds(self):
        self.assertAlmostEqual(6.7+0,2+4.7)
        self.assertAlmostEqual(6.7+1,2+5.7)
    def test_efficiency_monotonic(self):self.assertGreater(minimum_time(C,V,P,.5),minimum_time(C,V,P))
    def test_zero_time_zero_voltage(self):self.assertEqual(max_voltage_at(C,0,P),0)

if __name__=="__main__":
    unittest.main(verbosity=2)
