"""Source-bounded Filsinger polarity countermodels; no real netlist asserted."""
from fractions import Fraction as F
from math import cos, pi, sqrt
import unittest

WHITE_CAP = F(333,100_000_000)  # 3.33 microfarad, original narration
V_TARGET = F(1500)
POWER = F(67,10)  # reported, conditionally interpreted as electrical input

def energy(c,v):
    return c*v*v/2

def terminals(v_return, v_across_cap):
    return v_return+v_across_cap, v_return

def lc_voltage(c, l, initial_v, seconds):
    return float(initial_v)*cos(seconds/sqrt(float(c*l)))

class SourceBoundCountermodels(unittest.TestCase):
    def test_capacitor_energy(self):
        self.assertEqual(energy(WHITE_CAP,V_TARGET),F(2997,800))

    def test_ground_reference_flip_without_capacitor_reversal(self):
        # One meter terminal crosses the zero of an independent reference.
        # The SAME capacitor maintains a positive 1500-V differential.
        a, a_return=terminals(F(-1000),V_TARGET)
        b, b_return=terminals(F(-1600),V_TARGET)
        self.assertEqual((a,b),(500,-100))
        self.assertEqual(a-a_return,V_TARGET)
        self.assertEqual(b-b_return,V_TARGET)

    def test_actual_lc_polarity_reversal_without_new_source(self):
        l=125e-6  # hypothetical tank inductor, NOT measured
        c=float(WHITE_CAP)
        f=1/(2*pi*sqrt(l*c))
        self.assertAlmostEqual(f,7800,delta=5)
        self.assertAlmostEqual(lc_voltage(c,l,1500,0),1500,delta=1e-7)
        self.assertAlmostEqual(lc_voltage(c,l,1500,1/(2*f)),-1500,delta=1e-7)
        self.assertAlmostEqual(energy(c,1500),energy(c,-1500))

    def test_full_dissipative_recharge_is_not_available_at_6p7w(self):
        required=energy(WHITE_CAP,V_TARGET)*7800
        self.assertEqual(required,F(116883,4)) # 29,220.75 W
        self.assertGreater(required,POWER)
        self.assertLess(POWER/7800,energy(WHITE_CAP,V_TARGET))

    def test_environmental_power_not_identified_by_visible_drive(self):
        # Both worlds have identical drive (6.7W) and load (2W).
        for ambient,loss in [(F(0),F(47,10)),(F(1),F(57,10))]:
            self.assertEqual(POWER+ambient,F(2)+loss)

if __name__=="__main__":
    unittest.main(verbosity=2)
