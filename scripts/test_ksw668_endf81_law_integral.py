#!/usr/bin/env python3
"""Seven exact synthetic ENDF law/continuity negative controls (NOT data)."""
import unittest,math
import ksw668_endf81_c2_law_integral as M

def grid(rows,law):
    return {"original_sha256":"SYNTHETIC-ONLY",
            "pairs":rows,"interpolations":[(len(rows),law)]}

class EndfLawTests(unittest.TestCase):
    def rate(self,rows,law,a,b):
        return M.integrate_source(grid(rows,law),[(a,1.),(b,1.)],1e24,
                                  "synthetic deterministic verification")["modelled_reactions_per_second"]
    def test_histogram_jump_not_trapezoid(self):
        self.assertAlmostEqual(self.rate([(1,2),(2,40),(3,80)],1,1,3),42,places=10)
    def test_linear_law_and_linear_flux_product(self):
        g=grid([(1,2),(3,6)],2)
        r=M.integrate_source(g,[(1,1),(3,3)],1e24,"synthetic")
        self.assertAlmostEqual(r["modelled_reactions_per_second"],52/3,places=10)
    def test_law3_linear_log_energy(self):
        self.assertAlmostEqual(self.rate([(1,1),(math.e,2)],3,1,math.e),math.e,places=9)
    def test_law4_log_sigma_linear_energy(self):
        self.assertAlmostEqual(self.rate([(1,1),(2,math.e)],4,1,2),math.e-1,places=9)
    def test_law5_powerlaw(self):
        self.assertAlmostEqual(self.rate([(1,1),(4,16)],5,1,4),21,places=9)
    def test_repeated_knot_jump(self):
        self.assertAlmostEqual(
            self.rate([(1,1),(2,2),(2,20),(3,20)],2,1,3),21.5,places=9)
    def test_fail_closed_source_and_energy_domain(self):
        with self.assertRaises(ValueError):
            M.integrate_source(grid([(1,1),(2,2)],2),[(.5,1),(2,1)],1,"synthetic")
        with self.assertRaises(ValueError):
            M.integrate_source(grid([(1,1),(2,2)],2),[(1,1),(3,1)],1,"synthetic")
        with self.assertRaises(ValueError):
            M.integrate_source(grid([(1,1),(2,2)],2),[(1,1),(2,1)],1,"")

if __name__=="__main__":
    unittest.main(verbosity=2)
