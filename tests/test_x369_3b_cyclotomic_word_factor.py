import unittest
from fractions import Fraction as F
from scripts.x369_3b_cyclotomic_rank import Q,ONE,ZERO,OMEGA
from scripts.x369_3b_cyclotomic_word_factor import Mat,apply_reference,normalize
from scripts.x369_3b_nonzero_weyl_trace import WEIGHTS,Z


class WordFactor(unittest.TestCase):
    def test_exact_matrix_arithmetic(self):
        A=Mat.read([[['1/2','1/3'],['0','1']],[['1','0'],['-2/3','1/7']]])
        B=Mat.read([[['2','0'],['0','1']],[['-1','2'],['3/5','0']]])
        a=[[Q.wire(x) for x in row] for row in A.wire()]
        b=[[Q.wire(x) for x in row] for row in B.wire()]
        out=A.mul(B)
        expected=[[(a[i][0]*b[0][j]+a[i][1]*b[1][j]).pack() for j in range(2)] for i in range(2)]
        self.assertEqual(out.wire(),expected)
        self.assertTrue(A.scale(OMEGA).scale(OMEGA.inv()).same(A))
        self.assertTrue(A.mul(Mat.identity(2)).same(A))

    def test_reference_scalar_is_not_discarded(self):
        e=[tuple(int(i==j) for i in range(6)) for j in range(6)]
        aa=[(a,Z,0) for a in e]
        phi=[ZERO]*729;phi[0]=ONE
        v=[ZERO]*729;v[1]=OMEGA
        for p in (1,2):
            self.assertEqual(apply_reference(phi,aa,p,v),v)
        q,M,s,k=normalize(v,Mat.identity(2))
        self.assertEqual(s,OMEGA);self.assertEqual(k,WEIGHTS[1])
        self.assertEqual(q[1],ONE)
        self.assertTrue(M.same(Mat.identity(2).scale(OMEGA)))

if __name__=='__main__':unittest.main()
