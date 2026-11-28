"""Portable exact inverse/sector ordering; actual MMV requires mmgroup."""
import unittest
from itertools import islice
import numpy as np
from scripts.x369_actual_weyl_frame_bidi import RowBasis,inverse7
from scripts.monster_2b_mmgroup_matrix_free_intertwiner import candidates


class WeylFrameBidi(unittest.TestCase):
    def test_actual_sector_order(self):
        labels=list(islice(candidates(),48))
        self.assertEqual(labels,[('Y',0,j) for j in range(24)]+[('Z',0,j) for j in range(24)])

    def test_exact_rank_and_inverse(self):
        for n in (24,90):
            rng=np.random.default_rng(n)
            # Construct invertible triangular factors without guessing rank.
            L=np.tril(rng.integers(0,7,(n,n)),-1)+np.eye(n,dtype=np.int64)
            U=np.triu(rng.integers(0,7,(n,n)),1)+np.eye(n,dtype=np.int64)
            M=L@U%7
            b=RowBasis()
            for c in M.T:self.assertTrue(b.add(c))
            self.assertFalse(b.add((M[:,0]+2*M[:,1])%7))
            inv=inverse7(M[b.pivots,:])
            self.assertTrue(np.array_equal(inv@M[b.pivots,:]%7,np.eye(n,dtype=np.int64)))
            v=rng.integers(0,7,n)
            self.assertTrue(np.array_equal(inv@(M@v%7)[b.pivots]%7,v))
        with self.assertRaises(ValueError):inverse7([[1,1],[2,2]])

if __name__=='__main__':unittest.main()
