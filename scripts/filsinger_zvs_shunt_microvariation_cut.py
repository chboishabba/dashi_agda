#!/usr/bin/env python3
"""Conditional shunt-resistor / oscillator-microvariation maximum cut.
A 7.8kHz ACOUSTIC peak is not proof of an electrical switching frequency.
The 1MΩ shunt statement is a SOURCE CLAIM, not a measured terminal resistance.
"""
from math import pi, sqrt, log
import unittest

C=3.33e-6
R=1e6
F_AUDIO=7800.
P=6.7

def f_rc(r,c):return 1/(2*pi*r*c)
def bleed_loss(v,r):return v*v/r
def q_shunt(r,c,f):return 2*pi*f*r*c
def damped_frequency_ratio(q):return sqrt(1-1/(4*q*q))
def charge_time_with_shunt(v,p,r,c,n=1):
    x=n*v*v/(p*r)
    return -r*c/2*log(1-x) if x<1 else float('inf')

class Tests(unittest.TestCase):
    def test_rc_tau(self):self.assertAlmostEqual(R*C,3.33)
    def test_rc_frequency(self):self.assertAlmostEqual(f_rc(R,C),.0477942772)
    def test_not_7p8khz(self):self.assertLess(f_rc(R,C),.1)
    def test_q_shunt(self):self.assertAlmostEqual(q_shunt(R,C,F_AUDIO),163199.4551687)
    def test_small_direct_damped_shift(self):
        self.assertLess(1-damped_frequency_ratio(q_shunt(R,C,F_AUDIO)),1e-10)
    def test_small_relative_loss_if_q_100(self):
        self.assertLess(100/q_shunt(R,C,F_AUDIO),.001)
    def test_bleed_power_one(self):self.assertEqual(bleed_loss(1500,R),2.25)
    def test_bleed_power_two(self):self.assertEqual(2*bleed_loss(1500,R),4.5)
    def test_available_budget_two(self):self.assertAlmostEqual(P-4.5,2.2)
    def test_one_charge(self):self.assertTrue(.67<charge_time_with_shunt(1500,P,R,C)<.70)
    def test_two_charge(self):self.assertTrue(1.8<charge_time_with_shunt(1500,P,R,C,2)<1.9)
    def test_other_cap_rc(self):self.assertEqual(2e-6*2e6,4)
    def test_power_10kv_2meg(self):self.assertEqual(10000**2/2e6,50)
    def test_100ua_meter(self):self.assertEqual(10000/(100e-6),1e8)
if __name__=="__main__":unittest.main(verbosity=2)
