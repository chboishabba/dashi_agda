"""Finite support regression for the exact 3-4-5 Fourier witness.

This test checks the combinatorial distinction used by Agda R851:
opposite active seed pairs DO occur at output zero, while the only
nonzero outputs inside the radius-four cube are the eight selected modes.
It is not an Agda kernel receipt.
"""
from itertools import product
import unittest

SEEDS = {
    (3,0,0), (-3,0,0), (0,4,0), (0,-4,0),
    (3,4,0), (-3,-4,0),
}
OUTPUTS = {
    (-3,-4,0), (-3,0,0), (-3,4,0), (0,-4,0),
    (0,4,0), (3,-4,0), (3,0,0), (3,4,0),
}
def add(p,q):
    return tuple(a+b for a,b in zip(p,q))

class Rational345OutputSupport(unittest.TestCase):
    def test_zero_output_active_pairs_not_empty(self):
        zero_pairs=[(p,q) for p,q in product(SEEDS,repeat=2)
                    if add(p,q)==(0,0,0)]
        self.assertEqual(len(zero_pairs),6)
        self.assertTrue(all(q==tuple(-a for a in p) for p,q in zero_pairs))

    def test_nonzero_output_sparse_support(self):
        in_cube={add(p,q) for p,q in product(SEEDS,repeat=2)
                 if all(abs(x)<=4 for x in add(p,q))}
        self.assertEqual(in_cube,OUTPUTS|{(0,0,0)})
        self.assertEqual(in_cube-{(0,0,0)},OUTPUTS)

if __name__=="__main__":
    unittest.main()
