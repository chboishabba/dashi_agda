"""Exact scalar and exterior-algebra controls of the original RH/Hodge cuts.
No native kernel, analytic integrals or geometric K3 existence checked here.
"""
from fractions import Fraction as Q
from itertools import permutations
import unittest
import sympy as S

class Geometry(unittest.TestCase):
    def test_relative_gram_bound(self):
        # Plateau enlarged within (0, log 2), retaining every prime port.
        a,b=S.Rational(1,16),S.Rational(5,8)
        H=S.Matrix(5,5,lambda i,j:(b**(2*(i+j)+1)-a**(2*(i+j)+1))/(2*(i+j)+1))
        D=S.Matrix(5,5,lambda i,j:0 if i*j==0 else 4*i*j*(b**(2*(i+j)-1)-a**(2*(i+j)-1))/(2*(i+j)-1))
        for k in range(1,6):self.assertGreater(H[:k,:k].det(),0)
        inv=H.inv()
        for x,cap in [(a,17),(b,74)]:
            v=S.Matrix([x**(2*i) for i in range(5)])
            self.assertLess((v.T*inv*v)[0],cap)
        self.assertLess(S.trace(inv*D),53**2)
        # For cosh(u/2), cosh<2, cosh>=1, |derivative|<=cosh/2.
        self.assertLess(4/(b-a),17)
        ks=(1,2,14,15,17,18)
        for k in ks:
            row=sum(Q(1,2*k) if k==l else Q(1,abs(k-l))+Q(1,k+l) for l in ks)
            self.assertLess(row,Q(12,5))
        B=17+74+2*53
        self.assertEqual(B,197)
        self.assertLessEqual(Q(B,2)*Q(12,5)/946,Q(1,4))
        self.assertLess(S.Rational(21,32),S.Rational(2,3))

    def test_cubic_separability_projector(self):
        x,y=S.symbols('x y');f=x**3+x**2-2*x-1;g=f.subs(x,y)
        inv=S.invert(S.diff(f,x),f,x)
        e=S.expand(S.cancel((f-g)/(x-y))*inv)
        def red(p):return S.rem(S.rem(S.expand(p),f,x),g,y).expand()
        e=red(e)
        self.assertEqual(red(e*e-e),0)
        self.assertEqual(red((x-y)*e),0)
        self.assertEqual(S.rem(e.subs(y,x),f,x),1)
        self.assertEqual(red(e-e.xreplace({x:y,y:x})),0)

    def test_skew_cayley_and_pfaffian(self):
        # Model of a nonzero anti-self-adjoint CM direction, not an actual K3.
        J=S.diag(*([S.Matrix([[0,-1],[1,0]])]*3));I=S.eye(6)
        U=(I+J)*(I-J).inv();K=U-U.inv()
        self.assertEqual(U.T*U,I)
        self.assertEqual(K.T,-K);self.assertNotEqual(K.det(),0)
        def alt_pair(M):
            total=0
            for p in permutations(range(6)):
                sign=(-1)**sum(p[i]>p[j] for i in range(6) for j in range(i+1,6))
                total+=sign*M[p[0],p[1]]*M[p[2],p[3]]*M[p[4],p[5]]
            return total
        # 2^3*3! times the Pfaffian; ordinary symmetric pairing is killed.
        self.assertEqual(alt_pair(K)**2,48**2*K.det())
        self.assertNotEqual(alt_pair(K),0)
        self.assertEqual(alt_pair(I),0)

if __name__=='__main__':unittest.main()
