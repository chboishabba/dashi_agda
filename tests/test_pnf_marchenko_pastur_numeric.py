"""Synthetic-only tests of the MP numerical backend."""
import unittest
import numpy as np
from scripts.pnf_marchenko_pastur_numeric import MPNull, covariance, clean, receipt

class MPTests(unittest.TestCase):
    def test_density_atom_and_edges(self):
        for q in (0.25,0.6,1.0,2.0,4.0):
            mp = MPNull(q)
            lo, hi = mp.edges
            t = np.linspace(1e-9, np.pi-1e-9, 100001)
            x = (lo+hi)/2 + (hi-lo)*np.cos(t)/2
            mass = np.trapezoid(mp.density(x)*(hi-lo)*np.sin(t)/2,t)
            self.assertAlmostEqual(mass+mp.zero_atom, 1, delta=2e-4)
    def test_rank_and_diagonal(self):
        x = np.random.default_rng(42).normal(size=(12,20))
        c = covariance(x)
        self.assertAlmostEqual(np.trace(c),20)
        out, d = clean(c,MPNull(20/11))
        self.assertGreaterEqual(d["forced_zero_modes_observed"],9)
        self.assertTrue(np.allclose(np.diag(out),1))
        self.assertGreaterEqual(np.linalg.eigvalsh(out)[0],-1e-8)
    def test_source_guards(self):
        with self.assertRaises(ValueError): MPNull(0)
        with self.assertRaises(ValueError): covariance(np.ones((10,3)))
        with self.assertRaises(ValueError): covariance(np.full((5,3),np.nan))
        with self.assertRaises(ValueError): receipt(np.ones((3,2)),"","returns")
    def test_synthetic_factor_vs_shuffle(self):
        rng = np.random.default_rng(20261109)
        n,p,rho = 200,120,.25
        x = np.sqrt(rho)*rng.normal(size=(n,1))+np.sqrt(1-rho)*rng.normal(size=(n,p))
        shuffled = np.column_stack([x[rng.permutation(n),i] for i in range(p)])
        a = receipt(x,"synthetic","returns")
        b = receipt(shuffled,"synthetic_shuffled","returns")
        self.assertGreater(a["above_edge"],0)
        self.assertTrue(a["cleaned_psd"] and b["cleaned_psd"])
        self.assertTrue(a["cleaned_unit_diagonal"] and b["cleaned_unit_diagonal"])

if __name__=="__main__":
    unittest.main()
