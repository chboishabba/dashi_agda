import unittest
from time import monotonic
import numpy as np
from scripts.x369_3b_normalizer_coset_action import Chart,bch,path_between,partition
from scripts.x369_3b_E_coset_normal_form import normal_form
from scripts.x369_actual_3b_atlas_quotient_alignment import J


class CosetAction(unittest.TestCase):
    def test_batched_matches_scalar(self):
        rng=np.random.default_rng(369)
        for sign in (1,2):
            for _ in range(4):
                L=np.eye(13,dtype=np.int64)
                L[6:12,6:12]*=sign;L[12,12]=sign
                L[12,:12]=rng.integers(0,3,12)
                c=Chart(L)
                e=rng.integers(0,3,(30,13))
                expected=np.stack([normal_form(L,x)[0] for x in e])
                self.assertTrue(np.array_equal(c.canonical(e),expected))

    def test_full_small_fibre_and_centralizer_permutation(self):
        L=np.eye(13,dtype=np.int64);L[:12,:12]*=2
        c=Chart(L);q,labels=c.inventory()
        self.assertEqual(len(q),3)
        K=np.eye(13,dtype=np.int64);K[6:12,6:12]*=2;K[12,12]=2
        p=c.permutation(q,labels,K,np.zeros(13,dtype=np.int64))
        self.assertEqual(p.tolist(),[0,2,1])
        self.assertEqual(partition([p],3,monotonic()+5),[1,2])
        self.assertEqual(path_between([p],1,2,monotonic()+5)[0],[0])
        self.assertEqual(path_between([p],0,2,monotonic()+5),(None,1,True))

    def test_identity_full_inventory(self):
        c=Chart(np.eye(13,dtype=np.int64));q,labels=c.inventory()
        self.assertEqual(len(q),3**12+2)
        self.assertTrue(np.array_equal(c.canonical(q[::1000]),q[::1000]))
        self.assertEqual(labels[:3].tolist(),[0,1,2])

if __name__=='__main__':unittest.main()
