import unittest
from fractions import Fraction as F
import numpy as np
from scripts.x369_3b_cyclotomic_projector import CV,zero,NORM
from scripts.x369_monster_dyadic_source_action import unit
from scripts.x369_3b_cyclotomic_rank import Q,ONE,ZERO,OMEGA,solve_matrix
from scripts.x369_3b_cyclotomic_normalizer import reference,monomial,WEIGHTS,sum_q


class CyclotomicWeld(unittest.TestCase):
    def test_field_and_vector_inverse(self):
        self.assertEqual(OMEGA*OMEGA+OMEGA+ONE,ZERO)
        for a in range(-3,4):
            for b in range(-3,4):
                x=Q(F(a),F(b))
                if x:self.assertEqual(x*x.inv(),ONE)
        v=CV(unit(300),unit(852))
        self.assertTrue(v.phase(1).phase(2).same(v))
        self.assertTrue(CV.reopen(v.wire()).same(v))
        self.assertTrue(np.array_equal(v.phase(1).residue(),2*v.residue()%7))
        self.assertEqual(NORM,2187)

    def test_exact_multiplicity_solve(self):
        M=[[ONE,OMEGA],[OMEGA,ONE]]
        c=[[Q(F(2,3),F(1,2))],[Q(F(-1,4),F(3))]]
        rhs=[[sum_q(x*y[0] for x,y in zip(row,c))] for row in M]
        self.assertEqual(solve_matrix(M,rhs),c)
        with self.assertRaises(ValueError):solve_matrix([[ONE,ONE],[ONE,ONE]],rhs)

    def test_both_reference_phases(self):
        zero=(0,)*6
        for p in (1,2):
            z=tuple(int(i==0) for i in range(6))
            mods=[(zero,tuple(int(i==j) for i in range(6)),0) for j in range(6)]
            v=reference(mods,p,zero)
            self.assertEqual(v[0],ONE);self.assertEqual(sum(bool(x) for x in v),1)
            mods=[(tuple(int(i==j) for i in range(6)),zero,0) for j in range(6)]
            v=reference(mods,p,zero)
            self.assertTrue(all(x==ONE for x in v))
            self.assertEqual(monomial(v,(z,zero,0),p),v)

if __name__=='__main__':unittest.main()
