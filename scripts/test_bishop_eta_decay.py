"""Exact regression for original eta decay and the selected Weil tenth tail.
Finite arithmetic controls, not native Bishop or Lean kernel acceptance.
"""
from fractions import Fraction as Q
from itertools import product
from math import factorial
import unittest
import sympy as S


def add(a, b):
    return a[0] + b[0], a[1] + b[1]


def mul(a, b):
    return a[0]*b[0] - a[1]*b[1], a[0]*b[1] + a[1]*b[0]


def scale(c, a):
    return c*a[0], c*a[1]


def norm1(a):
    return abs(a[0]) + abs(a[1])


def ceil(x):
    return -(-x.numerator // x.denominator)


def log_bounds(n, J):
    # Independent positive atanh remainder after dyadic range reduction.
    def unit(x):
        t = (x-1)/(x+1)
        lo = 2*sum((t**(2*j+1)/(2*j+1) for j in range(J)), Q(0))
        return lo, lo + 2*t**(2*J+1)/((2*J+1)*(1-t*t))
    k = n.bit_length()-1
    lo, hi = unit(Q(n, 2**k))
    a, b = unit(Q(2))
    return lo+k*a, hi+k*b


def dirichlet_enclosure(n, s, J=40):
    """Exact Gaussian rational center, rigorous l1 error for n**(-s)."""
    lo, hi = log_bounds(n, J)
    z = scale(-(lo+hi)/2, s)
    rho = norm1(z)
    perturb = norm1(s)*(hi-lo)/2
    degree = max(J, ceil(2*rho))
    p = term = (Q(1), Q(0))
    for j in range(1, degree+1):
        term = scale(Q(1,j), mul(term,z))
        p = add(p,term)
    # Taylor geometric tail plus exponential sensitivity on the log segment.
    error = 2*rho**(degree+1)/factorial(degree+1)
    error += perturb*3**ceil(rho+perturb)
    return p, error


def potential(n, C, delta):
    return C/Q((2*n+1)**delta)


class OriginalDecayTests(unittest.TestCase):
    def test_symbolic_telescoping_and_pair_source(self):
        a,b,c,x,y,z = S.symbols('a b c x y z', real=True)
        self.assertEqual(S.expand((a-b)+(b-c)-(a-c)), 0)
        self.assertEqual(S.expand((y-z)+(x-y)-(x-z)), 0)
        self.assertEqual(S.expand((a+b)-a-b), 0)

    def test_original_real_pair_all_cutoffs(self):
        for sigma, delta in product(range(1,5), range(1,5)):
            if delta > sigma:
                continue
            C = Q(sigma,delta)
            prefix = [Q(0)]
            for n in range(32):
                block = Q(1,(2*n+1)**sigma)-Q(1,(2*n+2)**sigma)
                self.assertLessEqual(abs(block), potential(n,C,delta)-potential(n+1,C,delta))
                prefix.append(prefix[-1]+block)
            for n in range(33):
                for m in range(n,33):
                    self.assertLessEqual(abs(prefix[m]-prefix[n]),potential(n,C,delta)-potential(m,C,delta))
                    self.assertLessEqual(abs(prefix[n]-prefix[m]),potential(n,C,delta))

    def test_original_complex_pair_and_tail(self):
        for sigma,tau,delta in [(Q(1),Q(1),1),(Q(1),Q(-3,2),1),
                                (Q(3,2),Q(2),1),(Q(2),Q(-3,4),2)]:
            C = (abs(sigma)+abs(tau))/delta
            prefix = [((Q(0),Q(0)),Q(0))]
            terms = [dirichlet_enclosure(n,(sigma,tau)) for n in range(1,17)]
            for n in range(8):
                a,ea = terms[2*n]
                b,eb = terms[2*n+1]
                block = add(a,scale(-1,b))
                err = ea+eb
                bound = potential(n,C,delta)-potential(n+1,C,delta)
                self.assertLessEqual(sum((abs(x)+err)**2 for x in block),bound**2)
                old, eo = prefix[-1]
                prefix.append((add(old,block),eo+err))
            for n in range(9):
                for m in range(n+1,9):
                    a,ea = prefix[m]
                    b,eb = prefix[n]
                    diff = add(a,scale(-1,b))
                    bound = potential(n,C,delta)-potential(m,C,delta)
                    self.assertLessEqual(sum((abs(x)+ea+eb)**2 for x in diff),bound**2)

    def test_dyadic_native_modulus(self):
        for C,delta,k in product((Q(0),Q(1),Q(7,3)),(1,2,3),(1,3,17,256)):
            q = Q(1,2**delta)
            K,index = 0,0
            while C*q**K > Q(1,k):
                K += 1
                index = 2*index+1
            self.assertEqual(index+1,2**K)
            self.assertEqual(Q(1,(index+1)**delta),q**K)
            for n in (index+1,index+2,2*index+3):
                self.assertLessEqual(potential(n,C,delta),C*q**K)
                self.assertLessEqual(potential(n,C,delta),Q(1,k))

    def test_weil_even_harmonic_remainder(self):
        a,b,u = S.symbols('a b u',real=True)
        polynomial = sum(S.re((a+S.I*b)**(2*j))/factorial(2*j) for j in range(5))
        literal = S.series(S.cosh(a*u)*S.cos(b*u),u,0,10).removeO().subs(u,1)
        self.assertEqual(S.expand(polynomial-literal),0)
        # For radius squared <=2, each normalized even-tail ratio is <=1/66.
        # A second-shell refinement uses the sharper subsequent ratio <=1/91.
        sharp = 1+Q(1,66)/(1-Q(1,91))
        self.assertLess(sharp,Q(66,65))
        for r2 in (Q(0),Q(1,3),Q(1),Q(3,2),Q(2)):
            for j in range(5,25):
                self.assertLessEqual(r2/((2*j+1)*(2*j+2)),Q(1,66))
                if j>=6:
                    self.assertLessEqual(r2/((2*j+1)*(2*j+2)),Q(1,91))
            normalized = sum(r2**j*Q(factorial(10),factorial(10+2*j)) for j in range(20))
            self.assertLessEqual(normalized,sharp)
            self.assertLessEqual(normalized,Q(66,65))


if __name__ == '__main__':
    unittest.main()
