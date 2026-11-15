#!/usr/bin/env python3
"""Synthetic ONE coherent incident wave, two orthogonal loaded modes.
Physics assumptions and source promotion in Docs/research/SmithFilsingerGoldenFibonacciSingleWaveMaxCut20261112.md.
No Maxwell boundary simulation or measured environmental watts claimed.
"""
from math import sqrt
import unittest
PHI=(1+sqrt(5))/2
GE,GI=.04,.02
RATIOS={"square":1.0,"3:2":1.5,"5:3":5/3,"8:5":8/5,"13:8":13/8,"21:13":21/13,"golden":PHI}
def response(r,tx=1.0,ty=1.0,load=.04):
    g=GE+GI+load
    # Single 45-degree linear plane-wave field; two orthogonal projections,
    # source power normalized to one, not two incident independent waves.
    ax=sqrt(GE)/complex(g,tx/sqrt(r)-1)
    ay=sqrt(GE)/complex(g,ty*sqrt(r)-1)
    n=abs(ax)**2+abs(ay)**2
    return {"circularity":2*(ax.conjugate()*ay).imag/n,
            "useful":2*load*n, "fx":tx/sqrt(r), "fy":ty*sqrt(r)}
def quadrature_tunings(r,load=.04):
    g=GE+GI+load
    return (1-g)*sqrt(r),(1+g)/sqrt(r)
class Tests(unittest.TestCase):
    def test_phi_equation(self):self.assertAlmostEqual(PHI**2,PHI+1)
    def test_one_source_normalization(self):self.assertAlmostEqual(response(1)["useful"],.64)
    def test_square_linear(self):self.assertAlmostEqual(response(1)["circularity"],0)
    def test_golden_untuned(self):
        x=response(PHI)
        self.assertAlmostEqual(abs(x["circularity"]),.6954590264640,places=9)
        self.assertAlmostEqual(x["useful"],.0955160780743,places=9)
    def test_golden_tuned(self):
        tx,ty=quadrature_tunings(PHI)
        x=response(PHI,tx,ty)
        self.assertAlmostEqual(abs(x["circularity"]),1)
        self.assertAlmostEqual(x["useful"],.32)
    def test_tuning_not_free(self):
        tx,ty=quadrature_tunings(PHI)
        self.assertGreater(tx-1,.14)
        self.assertGreater(1-ty,.13)
    def test_power_bound(self):
        for r in RATIOS.values():
            for load in (.005,.02,.04,.06,.1,.2):
                self.assertLessEqual(response(r,load=load)["useful"],1+1e-12)
    def test_fibonacci(self):self.assertLess(abs(PHI-21/13),abs(PHI-3/2))
    def test_smith_ratio_not_phi(self):self.assertNotEqual(4,PHI)
if __name__=="__main__":
    unittest.main(verbosity=2)
    for name,r in RATIOS.items():
        print(name,r,response(r),quadrature_tunings(r))
