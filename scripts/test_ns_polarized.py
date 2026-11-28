import unittest
from fractions import Fraction as Q
from itertools import product
import ns_polynomial_reference as n

class PolarizedTests(unittest.TestCase):
    def test_growth(self):
        self.assertEqual(n.polarized_growth(Q(3),Q(1)),Q(9,4))
        self.assertEqual(n.polarized_growth(Q(1,2),Q(1)),Q(0))
    def test_exact_complex_projection(self):
        # all transverse vectors built by the actual rational projector
        for k,l in product(((1,0,0),(0,1,0),(1,2,0),(1,0,1)),repeat=2):
            m=n.add(k,l)
            for a,b in product(((1,2,3,4,-1,2),(0,1,-2,1,3,0)),repeat=2):
                a=n.proj(k,a); b=n.proj(l,b)
                w=n.lin((1,n.bilinear({k:a},{l:b})),(1,n.bilinear({l:b},{k:a}))).get(m,n.ZERO)
                self.assertLessEqual(sum(x*x for x in w), n.lam(m)*sum(x*x for x in a)*sum(x*x for x in b))
    def test_critical_threshold_and_fixture(self):
        u=n.fixture(); path=n.build(u,2,Q(1,32),4)
        e,t=n.validate_polarized(path,u,Q(1))
        self.assertLess(e,n.validate_tight(path,u,Q(1))[0])
        self.assertLess(t,2)
    def test_previous_rejection_now_certified(self):
        u=n.lin((1,n.cos_mode((0,1,0),(1,0,0),Q(2))),
                (1,n.cos_mode((1,0,0),(0,0,1),Q(1,4))),
                (1,n.cos_mode((1,0,1),(0,1,0),Q(1,4))))
        path=n.build(u,2,Q(1,32),16)
        self.assertEqual(n.validate_polarized(path,u,Q(1)),
                         (Q(163742933,5000000000),Q(959309167,625000000)))
    def test_reject_invalid_budget(self):
        with self.assertRaises(ValueError): n.validate_polarized([],{},Q(1),Q(2))
        with self.assertRaises(ValueError): n.validate_polarized([],{},Q(1),initial_tail=Q(-1))

if __name__=='__main__': unittest.main()
