import unittest
from fractions import Fraction as Q
from itertools import product
import sympy as S
import bishop_eta_multibase as m

class MultiBaseTests(unittest.TestCase):
    def test_symbolic_diamond(self):
        a,b,c,d,p,q=S.symbols('a b c d p q',complex=True)
        self.assertEqual(S.expand((a-p*b)+p*(b-q*d)-(a-q*c)-q*(c-p*d)),0)

    def test_original_integer_source(self):
        for s,b,c,n in product((-2,0,1,2,3),range(2,7),range(2,7),range(6)):
            a=lambda j: Q(j)**(-s)
            partial=lambda N: sum((a(j) for j in range(1,N+1)),Q(0))
            P,Qc=b*a(b),c*a(c)
            D=lambda h,N: partial(h*N)-h*a(h)*partial(N)
            self.assertEqual(D(b,n),sum(((1-b*int(j%b==0))*a(j) for j in range(1,b*n+1)),Q(0)))
            self.assertEqual(D(b,c*n)+P*D(c,n),D(c,b*n)+Qc*D(b,n))

    def test_log_enclosures(self):
        for b in range(1,20):
            lo,hi=m.log_nat_bounds(b,6)
            l2,h2=m.log_nat_bounds(b,12)
            self.assertLessEqual(lo,l2)
            self.assertLessEqual(h2,hi)
            self.assertLessEqual(l2,h2)

    def test_divisor_exact_real_controls(self):
        for b,s in product(range(2,8),(-2,-1,0,1,2,3)):
            p,e=m.divisor_enclosure(Q(s),0,b,16)
            self.assertLessEqual(m.l1(m.add(p,(-(1-Q(b)**(1-s)),Q(0)))),e)

    def test_adjacent_selector(self):
        for s,t in [(Q(1,2),Q(0)),(Q(1),Q(9)),(Q(1),Q(1,100)),(Q(1001,1000),Q(0)),(Q(2),Q(3)),(Q(1),Q(-9))]:
            a,b,gap=m.adjacent_bases(s,t)
            base,lower=m.choose_divisor(s,t,max_terms=256)
            self.assertIn(base,(a,b))
            self.assertGreaterEqual(lower,gap/2)
            p,e=m.divisor_enclosure(s,t,base,128)
            self.assertGreater(max(abs(p[0]),abs(p[1]))-e,0)

    def test_tail_cutoffs_and_rejection(self):
        for b,d,r,e in product((2,3,7),(Q(1,2),Q(1),Q(3)),(Q(3),Q(5)),(Q(1,10),Q(1,1000))):
            k=m.cutoff_exponent(b,d,r,e,256)
            self.assertLessEqual(m.tail_bound(b,d,r,k),e)
            if k:
                self.assertGreater(m.tail_bound(b,d,r,k-1),e)
        with self.assertRaises(ValueError): m.choose_divisor(1,0)
        with self.assertRaises(ValueError): m.choose_divisor(1,1000,max_terms=4)
        with self.assertRaises(ValueError): m.choose_divisor(0.5,0)
        with self.assertRaises(ValueError): m.log_unit_interval(1.5,8)
        with self.assertRaises(ValueError): m.exp_enclosure((0.5,0),8)
        with self.assertRaises(ValueError): m.cutoff_exponent(2,Q(1,2),5,Q(1,100),1)

    def test_exact_integer_periodic_tails(self):
        for b,s,k in product(range(2,7),range(1,5),range(6)):
            for N in (2**k,2**k+1,2**k+b):
                M=N+3*b+1
                t=sum(((1-b*int(j%b==0))*Q(1,j**s) for j in range(N,M+1)),Q(0))
                self.assertLessEqual(abs(t),m.tail_bound(b,s,s,k))

if __name__=='__main__': unittest.main()
