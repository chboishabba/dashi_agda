import unittest
from fractions import Fraction
import numpy as np
from sympy import Matrix,diag
from scripts.x369_actual_conway_real_lift import short_frame,orient,canonical,signed_composition
from scripts.x369_actual_dyadic_griess_product import add,times,zero,ROW_BOUND
from scripts.x369_monster_dyadic_source_action import unit,MODULUS,DIGIT_BASE
from scripts.x369_3b_normalizer_cocycle_composition import Factor,compose,exact_equal,invert_coord
from scripts.x369_actual_3b_normalizer_tensor import monomial,ZERO


class SourceWeld(unittest.TestCase):
    def test_exact_short_frame_orientation(self):
        B=short_frame()
        P=Matrix.eye(24)[:,::-1]
        for j in range(4):
            s=diag(*[(-1)**int((i+j)%3==0) for i in range(24)])
            R=canonical(orient(B,P*B*s)*B.inv())
            self.assertEqual(R,canonical(P))
            self.assertEqual(R.T*R,Matrix.eye(24))
            self.assertIn(signed_composition(R,R.T,Matrix.eye(24)),(0,1))
        with self.assertRaises(ValueError):orient(B,2*B)

    def test_dyadic_linear_terms(self):
        v=unit(0);w=unit(300)
        self.assertTrue(add(times(Fraction(1,2),v),times(Fraction(1,2),v)).same(v))
        self.assertTrue(add(times(-1,w),w).same(zero()))
        self.assertLess(2*ROW_BOUND*(DIGIT_BASE-1),MODULUS)
        with self.assertRaises(ValueError):times(Fraction(1,3),v)

    def test_normalized_factor_cocycle(self):
        # Small field matrices exercise scalar retention, not a source receipt.
        I=np.eye(2,dtype=np.int64)
        W=np.array([[0,1],[1,0]],dtype=np.int64)
        V=np.array([[1,1],[0,1]],dtype=np.int64)
        a=Factor(2,4,W,I)
        b=Factor(4,2,V,I)
        c=Factor(2,2,W,I)
        ab,_=compose(a,b);bc,_=compose(b,c)
        l,_=compose(ab,c);r,_=compose(a,bc)
        self.assertTrue(exact_equal(l,r))
        d=Factor(2,2,np.array([[1,2],[0,1]],dtype=np.int64),I)
        e=Factor(2,2,np.array([[1,0],[2,1]],dtype=np.int64),I)
        de,s=compose(d,e)
        self.assertIn(s,range(1,7))
        self.assertTrue(np.array_equal(np.kron(de.W,de.M)%7,
            np.kron(e.W,e.M)@np.kron(d.W,d.M)%7))
        with self.assertRaises(ValueError):compose(a,c)

    def test_reference_inverse(self):
        a=(1,2,0,1,2,0);b=(2,0,1,2,0,1)
        for z in (2,4):
            v=np.arange(729,dtype=np.int64)%7
            for t in range(3):
                c=(a,b,t)
                self.assertTrue(np.array_equal(monomial(monomial(v,c,z),invert_coord(c),z),v))

if __name__=='__main__':unittest.main()
