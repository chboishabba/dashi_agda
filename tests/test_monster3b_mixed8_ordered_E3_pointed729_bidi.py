#!/usr/bin/env python3
"""Independent finite-generator spot and total-bijection regressions."""
import sys
import unittest
from pathlib import Path
from itertools import product

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/"scripts"))
import monster3b_mixed8_ordered_E3_pointed729_bidi as model


class Pointed729Bidi(unittest.TestCase):
    def test_inverse_and_totality(self):
        for a,b,t in product(model.E,repeat=3):
            p=model.encode729(a,b,t)
            self.assertEqual(model.decode729(p),(a,b,t))
            if a==model.ZERO and b==model.ZERO:
                self.assertEqual(p[0],"central")
            else:
                self.assertEqual(p[0],"outer")

    def test_D4_equivariance(self):
        for a,b,t in product(model.E,repeat=3):
            p=model.encode729(a,b,t)
            for fn in (model.r,model.m):
                self.assertEqual(
                    model.encode729(*model.source_action((a,b,t),fn)),
                    model.target_action(p,fn))

    def test_census_and_nonpromotion(self):
        result=model.verify()
        self.assertEqual(result["source_80_D4_orbit_census"],{4:8,8:6})
        self.assertEqual(result["source_720_D4_orbit_census"],{4:24,8:78})
        self.assertEqual(result["D4_generator_equivariance_incidences"],1618)
        for k in ("ordered_E_splitting_canonically_selected",
                  "full_Heisenberg_equivariance","actual_Monster_intertwiner",
                  "IIT_causal_interpretation","Agda_kernel_verified"):
            self.assertFalse(result[k])


if __name__=="__main__":
    unittest.main()
