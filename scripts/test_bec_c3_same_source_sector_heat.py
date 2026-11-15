"""Run: python -m unittest discover -s scripts -p test_bec_c3_same_source_sector_heat.py"""
import unittest
from math import gamma,pi
import bec_c3_same_source_sector_heat as m
class TestSameSourceC3(unittest.TestCase):
    def test_exact_certificates(self):
        d=m.certificates()
        self.assertTrue(all(d.values()), d)
    def test_heat_sectors(self):
        for t in [0.,.1,1.,3.]:
            x,y=m.sector_heat(t)
            self.assertAlmostEqual(m.heat(t),x+y)
            self.assertAlmostEqual(m.twisted_heat(t),x-y/2)
    def test_zeta_sectors(self):
        for s in [1.5,2.,3.]:
            x,y=m.sector_zeta(s)
            self.assertAlmostEqual(m.spectral_zeta(s),x+y)
            self.assertAlmostEqual(m.spectral_zeta(s),
                sum(n*gamma(s)*E**(-s) for E,n in [(2.,1),(5.,2)])/gamma(s))
    def test_bose_not_bulk(self):
        self.assertEqual(m.sector_moment(0),(1,2))
        self.assertTrue(sum(m.bose_population(1.,0.))>0)
        with self.assertRaises(ValueError): m.bose_population(1.,2.)
    def test_zero_point_SI(self):
        h=6.62607015e-34
        self.assertAlmostEqual(m.zero_point(h/(2*pi)), 6*h/(2*pi))
if __name__ == '__main__':unittest.main()
