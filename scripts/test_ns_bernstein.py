import unittest
from fractions import Fraction as Q
import ns_polynomial_reference as n

class BernsteinTests(unittest.TestCase):
    def test_exact_basis(self):
        u=n.cos_mode((0,1,0),(1,0,0),Q(1))
        b=n.bernstein([u,n.lin((-2,u)),u])
        self.assertEqual(b,[u,{},{}])
    def test_nontrivial_old_fixture(self):
        u=n.fixture(); p=n.build(u,2,Q(1,32),16)
        e,t=n.validate_tight(p,u,Q(1))
        self.assertLess(e,Q(15978457,2500000000))
        self.assertLess(t,Q(1485422607,2000000000))
    def test_seams_and_rejection(self):
        u=n.cos_mode((0,1,0),(1,0,0),Q(1,16))
        e,t=n.validate_tight([(Q(1,8),[{}])],u,Q(1))
        self.assertGreaterEqual(e,Q(1,16))
        with self.assertRaises(ValueError): n.validate_tight([(Q(1),[{}])],n.fixture(),Q(1))
        with self.assertRaises(ValueError): n.validate_tight([(Q(1),[{}])],{},Q(1),Q(1))
    def test_certified_initial_tail(self):
        u=n.cos_mode((0,1,0),(1,0,0),Q(1,16))
        e,t=n.validate_tight([],u,Q(1),initial_tail=Q(1,32))
        self.assertEqual((e,t),(Q(1,32),Q(3,32)))
        self.assertGreaterEqual(n.cube_tail_upper(2,2,Q(1))**2,Q(26,24))
        with self.assertRaises(ValueError): n.validate_tight([],u,Q(1),initial_tail=Q(-1))
        with self.assertRaises(ValueError): n.validate_tight([],u,Q(1),initial_tail=Q(1,8))
    def test_larger_3d_case(self):
        u=n.lin((1,n.cos_mode((0,1,0),(1,0,0),Q(2))),(1,n.cos_mode((1,0,0),(0,0,1),Q(1,8))),(1,n.cos_mode((1,0,1),(0,1,0),Q(1,8))))
        p=n.build(u,2,Q(1,32),32)
        self.assertEqual(n.validate_tight(p,u,Q(1)),(Q(848497071,10000000000),Q(8926362043,10000000000)))
    def test_damped_growth(self):
        self.assertEqual(n.growth(Q(0),Q(3,4)),Q(0))
        self.assertEqual(n.growth(Q(3,4),Q(3,4)),Q(3,4))
        self.assertEqual(n.growth(Q(3,2),Q(3,4)),Q(3))

if __name__=='__main__': unittest.main()
