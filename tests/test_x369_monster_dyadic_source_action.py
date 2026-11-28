"""Exact integer reconstruction for the source atom contract, no MMV stub."""
import unittest
import numpy as np
from scripts.x369_monster_dyadic_source_action import (
    MODULI,MODULUS,SCALE,ROW_L1_BOUND,DIGIT_BASE,centered_crt,Dyadic,unit)


class DyadicSourceAction(unittest.TestCase):
    def test_unique_centered_crt(self):
        bound=ROW_L1_BOUND*(DIGIT_BASE-1)
        self.assertLess(2*bound,MODULUS)
        a=np.array([-bound,-129,-1,0,1,127,bound],dtype=np.int64)
        self.assertTrue(np.array_equal(centered_crt([a%p for p in MODULI],bound),a))
        with self.assertRaises(ValueError):centered_crt([a%p for p in MODULI],1)
        with self.assertRaises(ValueError):centered_crt([a%p for p in MODULI],MODULUS)

    def test_exact_dyadic_normalisation_and_residue(self):
        v=unit(852)
        w=Dyadic(v.numerator*SCALE,4)
        self.assertTrue(v.same(w))
        a=v.numerator.copy();a[0]=-3;a[852]=2
        w=Dyadic(a,3)
        self.assertEqual(w.sparse(),{'0':['-3/8','0'],'852':['1/4','0']})
        for p in MODULI:
            self.assertEqual(int(w.residue(p)[0]),-3*pow(8,-1,p)%p)
            self.assertEqual(int(w.residue(p)[852]),pow(4,-1,p))


if __name__=='__main__':unittest.main()
