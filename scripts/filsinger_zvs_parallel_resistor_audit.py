#!/usr/bin/env python3
"""Source-qualified analysis of parallel RC loads in the narrated Filsinger ZVS reel.
All real apparatus connections and electrical frequencies remain unverified.
"""
from math import pi, log, exp, sqrt
import unittest

C_WHITE = 3.33e-6  # reported
C_BLUE = 2e-6       # reported for alternate bank in new reel
P_DISPLAY = 6.7     # reported, conditional electrical real input
F_AUDIO = 7800.0    # acoustic only, not verified electrical oscillator frequency

def tau(r, c): return r*c
def corner(r,c): return 1/(2*pi*r*c)
def resistor_watts(v,r): return v*v/r
def capacitor_reactance(f,c): return 1/(2*pi*f*c)
def ideal_shunt_charging_time(v,p,r,c,n):
    """n equal uncharged RC banks receiving equal shares of constant REAL P,
    ignoring all losses except shunts. Infinite if target cannot be reached.
    """
    factor = n*v*v/(p*r)
    return -r*c/2*log(1-factor) if factor<1 else float('inf')
def ideal_shunt_voltage(t,p,r,c,n):
    return sqrt(p*r/n*(1-exp(-2*t/(r*c))))

class TestZVSShuntAudit(unittest.TestCase):
    def test_3p33u_1meg_tau(self):self.assertAlmostEqual(tau(1e6,C_WHITE),3.33)
    def test_3p33u_1meg_corner(self):self.assertAlmostEqual(corner(1e6,C_WHITE),.0477942772)
    def test_2u_1meg_tau(self):self.assertAlmostEqual(tau(1e6,C_BLUE),2)
    def test_2u_2meg_tau(self):self.assertAlmostEqual(tau(2e6,C_BLUE),4)
    def test_watts_one_resistor(self):self.assertAlmostEqual(resistor_watts(1500,1e6),2.25)
    def test_watts_two_resistors(self):self.assertAlmostEqual(2*resistor_watts(1500,1e6),4.5)
    def test_remainder_budget(self):self.assertAlmostEqual(P_DISPLAY-4.5,2.2)
    def test_10kv_2meg(self):self.assertAlmostEqual(resistor_watts(10000,2e6),50)
    def test_cap_reactance(self):self.assertAlmostEqual(capacitor_reactance(F_AUDIO,C_WHITE),6.1274714365)
    def test_shunt_is_large_at_audio_frequency(self):self.assertGreater(1e6/capacitor_reactance(F_AUDIO,C_WHITE),1e5)
    def test_meter_direct_scale(self):self.assertEqual(10000/(100e-6),100e6)
    def test_one_white_charging(self):self.assertAlmostEqual(ideal_shunt_charging_time(1500,P_DISPLAY,1e6,C_WHITE,1),.6813237113)
    def test_two_white_charging(self):self.assertAlmostEqual(ideal_shunt_charging_time(1500,P_DISPLAY,1e6,C_WHITE,2),1.8542275264)
    def test_two_blue_charging(self):self.assertAlmostEqual(ideal_shunt_charging_time(1500,P_DISPLAY,2e6,C_BLUE,2),.8184068604)
    def test_charging_roundtrip(self):
        t=ideal_shunt_charging_time(1500,P_DISPLAY,1e6,C_WHITE,2)
        self.assertAlmostEqual(ideal_shunt_voltage(t,P_DISPLAY,1e6,C_WHITE,2),1500)
    def test_unreachable_at_insufficient_power(self):
        self.assertEqual(ideal_shunt_charging_time(1500,4.5,1e6,C_WHITE,2),float('inf'))

if __name__=='__main__':unittest.main(verbosity=2)
