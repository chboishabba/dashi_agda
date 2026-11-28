import unittest
import numpy as np
from scripts.x369_3b_E_coset_normal_form import normal_form,conjugate,orbit_count


class ECoset(unittest.TestCase):
    def test_identity_and_parity_orbit_counts(self):
        L=np.eye(13,dtype=np.int64)
        self.assertEqual(orbit_count(L)['E_orbits'],3**12+2)
        e=np.zeros(13,dtype=np.int64);e[12]=2
        q,w,split=normal_form(L,e)
        self.assertTrue(split);self.assertTrue(np.array_equal(q,e))
        e[0]=1
        q,w,split=normal_form(L,e)
        self.assertFalse(split);self.assertEqual(q[12],0)
        L[:12,:12]*=2
        self.assertEqual(orbit_count(L)['E_orbits'],3)
        L=np.eye(13,dtype=np.int64);L[6:12,6:12]*=2;L[12,12]=2
        self.assertEqual(orbit_count(L)['E_orbits'],3**6)

    def test_canonical_conjugation_invariance(self):
        rng=np.random.default_rng(41)
        for sign in (1,2):
            for _ in range(30):
                L=np.eye(13,dtype=np.int64)
                L[6:12,6:12]*=sign;L[12,12]=sign
                L[12,:12]=rng.integers(0,3,12)
                e,x=rng.integers(0,3,(2,13))
                q,w,s=normal_form(L,e)
                self.assertTrue(np.array_equal(conjugate(L,e,w),q))
                r,_,t=normal_form(L,conjugate(L,e,x))
                self.assertTrue(np.array_equal(q,r))
                self.assertEqual(s,t)
                p,_,u=normal_form(L,q)
                self.assertTrue(np.array_equal(p,q))
                self.assertEqual(s,u)

if __name__=='__main__':unittest.main()
