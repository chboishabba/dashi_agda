import unittest
from fractions import Fraction as Q
import sympy as S
import ns_polynomial_reference as n

class ReferenceTests(unittest.TestCase):
    def test_exact_shear_and_zero(self):
        u=n.cos_mode((0,1,0),(1,0,0),Q(1,2))
        self.assertEqual(n.bilinear(u,u),{})
        self.assertEqual(n.validate([], {}, Q(1)), (Q(0),Q(0)))
    def test_full_3d_global_path(self):
        u=n.fixture()
        path=n.build(u, 2, Q(1,32), 16)
        bound,terminal=n.validate(path,u,Q(1))
        self.assertEqual(bound,Q(15978457,2500000000))
        self.assertEqual(terminal,Q(1485422607,2000000000))
        self.assertLess(terminal,1)
        self.assertTrue(any(n.lam(k)>4 for dt,p in path for row in n.residual(dt,p,Q(1)) for k in row))
    def test_independent_complex_convolution(self):
        u=n.fixture(); z={k:S.Matrix([S.Rational(a[j])+S.I*S.Rational(a[j+3]) for j in range(3)]) for k,a in u.items()}
        expected={}
        for k,a in z.items():
            for l,b in z.items():
                m=tuple(x+y for x,y in zip(k,l))
                if not any(m): continue
                mv=S.Matrix(m); P=S.eye(3)-mv*mv.T/mv.dot(mv)
                expected[m]=expected.get(m,S.zeros(3,1))+S.I*P*(a.dot(S.Matrix(l))*b)
        actual=n.bilinear(u,u)
        for k in set(expected)|set(actual):
            a=actual.get(k,n.ZERO)
            self.assertEqual(S.Matrix([S.Rational(a[j])+S.I*S.Rational(a[j+3]) for j in range(3)]),expected.get(k,S.zeros(3,1)))
    def test_seam_and_intra_step_residual(self):
        u=n.cos_mode((0,1,0),(1,0,0),Q(1,8))
        e,t=n.validate([(Q(1,8),[u])],u,Q(1))
        self.assertGreaterEqual(e,Q(1,64))
        e,t=n.validate([(Q(1,8),[{}])],u,Q(1))
        self.assertGreaterEqual(e,Q(1,8))
    def test_norm_enclosures(self):
        for j in range(1,40):
            x=Q(j,7); lo,hi=n.sqrt_bounds(x)
            self.assertLessEqual(lo*lo,x); self.assertGreaterEqual(hi*hi,x)
    def test_reject_bad_source(self):
        with self.assertRaises(ValueError): n.validate([], {(1,0,0):(Q(1),0,0,0,0,0)}, Q(1))
        with self.assertRaises(ValueError): n.validate([], {(0,1,0):(Q(1),0,0,0,0,0)}, Q(1))
        with self.assertRaises(ValueError): n.validate([], {(0,0,0):n.ZERO}, Q(1))
    def test_reject_bad_step(self):
        with self.assertRaises(ValueError): n.validate([(Q(0),[{}])], {}, Q(1))
        with self.assertRaises(ValueError): n.validate([(0.1,[{}])], {}, Q(1))
        with self.assertRaises(ValueError): n.validate([(Q(1),[])], {}, Q(1))
    def test_reject_large_error(self):
        with self.assertRaises(ValueError): n.validate([(Q(1),[{}])],n.cos_mode((0,1,0),(1,0,0),Q(2)),Q(1))

if __name__=='__main__': unittest.main()
