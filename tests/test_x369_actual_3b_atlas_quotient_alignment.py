import unittest
from pathlib import Path
import numpy as np
from scripts.x369_actual_3b_atlas_quotient_alignment import (
    I,J,mm,inverse,intertwiner,log_coord,group_coord,inner_offset,
    e_conjugator,atlas_matrices,candidates)
from time import monotonic


class AtlasAlignment(unittest.TestCase):
    def test_original_atlas_matrix_intertwiner(self):
        atlas=atlas_matrices(Path(__file__).resolve().parents[1])
        P=I.copy();P[0,1]=2;P[6,7]=1
        Pi=inverse(P)
        actual=[mm(mm(P,a),Pi) for a in atlas]
        Q,n=intertwiner(actual,atlas)
        self.assertEqual(n,1)
        self.assertIsNotNone(Q)
        self.assertTrue(np.array_equal(Q,P) or np.array_equal(Q,-P%3))
        found,stats=candidates(dict(C=actual[0],D=actual[1]),atlas,100,monotonic()+20)
        self.assertIsNotNone(found)

    def test_extraspecial_log_and_inner_action(self):
        a=(1,2,0,1,2,0);b=(0,1,2,0,1,2)
        for t in range(3):
            c=(a,b,t);self.assertEqual(group_coord(log_coord(c)),c)
        L=np.eye(13,dtype=np.int64);L[12,:12]=np.array((*b,*(-np.array(a)%3)))
        self.assertEqual(inner_offset(L),(a,b,0))
        self.assertIsNotNone(e_conjugator(L,((0,)*6,(0,)*6,1)))
        self.assertIsNone(e_conjugator(np.eye(13,dtype=np.int64),((0,)*6,(0,)*6,1)))

    def test_phase_inversion_and_general_conjugacy(self):
        L=np.eye(13,dtype=np.int64);L[6:12,6:12]=-I[:6,:6]%3;L[12,12]=2
        L[12,:12]=np.arange(12)%3
        rng=np.random.default_rng(41)
        for _ in range(30):
            v=rng.integers(0,3,13);u=L@v%3;d=(v-u)%3
            d[12]=(d[12]-2*int(v[:12]@J@u[:12]))%3
            x=e_conjugator(L,group_coord(d));self.assertIsNotNone(x)
            v=log_coord(x);u=L@v%3;q=(v-u)%3
            q[12]=(q[12]-2*int(v[:12]@J@u[:12]))%3
            self.assertTrue(np.array_equal(q,d))

if __name__=='__main__':unittest.main()
