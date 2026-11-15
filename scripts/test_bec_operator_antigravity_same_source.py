"""No CI required: python -m unittest discover -s scripts -p test_bec_operator_antigravity_same_source.py -v"""
import unittest
from fractions import Fraction as Q
from math import isclose
import bec_operator_antigravity_same_source as m

class TestOperatorAndStress(unittest.TestCase):
    def test_exact_certificates(self):
        checks=m.checks()
        self.assertTrue(all(checks.values()),checks)
    def test_operator_reversibility(self):
        self.assertEqual(m.mul(m.mul(m.T(m.U),m.Hobs),m.U),m.H)
    def test_both_sectors(self):
        self.assertEqual(m.sector_moment(0),(1,2))
        self.assertEqual(m.sector_moment(2),(4,50))
    def test_heat_zeta(self):
        for t in (0.,.5,2.):
            a,b=m.sector_heat(t)
            self.assertTrue(isclose(a+b,__import__("math").exp(-2*t)+2*__import__("math").exp(-5*t)))
        for s in (1.5,2.,3.):
            a,b=m.sector_zeta(s)
            self.assertTrue(isclose(a+b,2**(-s)+2*5**(-s)))
    def test_gravity_negative_control(self):
        self.assertEqual(m.stress(Q(3),0,0,0),(Q(-3),Q(3)))
        self.assertEqual(m.stress(Q(1),-1,-1,-1),(Q(-4),Q(-2)))

if __name__=="__main__": unittest.main()
