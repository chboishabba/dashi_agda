"""Finite exact controls for original factorial convolution and Nat-log/eta.
Not a check of Agda elaboration or of the analytic limit.
"""
import unittest
from fractions import Fraction as Q
from math import factorial
from itertools import product
import sympy as S


def term(x,n):
    q=x**n/factorial(n)
    return ((q,0),(0,q),(-q,0),(0,-q))[n%4]


def mul(a,b):
    return (a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0])


def total(terms):
    a=b=Q(0)
    for x,y in terms:
        a+=x; b+=y
    return a,b


class ImaginaryFactorialTests(unittest.TestCase):
    def test_arbitrary_symbolic_degree(self):
        x,y=S.symbols('x y',real=True)
        for n in range(13):
            conv=sum((S.I*x)**j*(S.I*y)**(n-j)/(factorial(j)*factorial(n-j)) for j in range(n+1))
            self.assertEqual(S.expand(conv-(S.I*(x+y))**n/factorial(n)),0)

    def test_exact_rectangle_triangle_wings(self):
        for x,y in product((Q(-2),Q(-1,3),Q(0),Q(1,2),Q(3)),repeat=2):
            for N in range(1,12):
                a=[term(x,j) for j in range(N)]
                b=[term(y,j) for j in range(N)]
                rectangle=mul(total(a),total(b))
                triangle=total(mul(a[j],b[k]) for j in range(N) for k in range(N-j))
                wing=total(mul(a[j],b[k]) for j in range(N) for k in range(N) if j+k>=N)
                self.assertEqual(rectangle,tuple(t+w for t,w in zip(triangle,wing)))
                self.assertEqual(triangle,total(term(x+y,j) for j in range(N)))
                bound=2*sum(abs(x)**j*abs(y)**k/(factorial(j)*factorial(k)) for j in range(2*N) for k in range(2*N-j) if j+k>=N)
                self.assertLessEqual(abs(wing[0]),bound)
                self.assertLessEqual(abs(wing[1]),bound)

class NatLogEtaTests(unittest.TestCase):
    def test_positive_natural_product_indices(self):
        for i,j in product(range(64),repeat=2):
            k=j+i*(j+1)
            self.assertEqual(k+1,(i+1)*(j+1))
        for k in range(128):
            self.assertEqual(2*k+2,2*(k+1))

    def test_original_log_product_enclosures(self):
        def partial(x,N):
            return sum((x**j/j for j in range(1,N+1)),Q(0))
        for m,n in product(range(1,13),repeat=2):
            x,y,z=Q(m-1,m),Q(n-1,n),Q(m*n-1,m*n)
            self.assertEqual(z,x+y-x*y)
            for N in (1,3,8,16,32):
                residual=partial(x,N)+partial(y,N)-partial(z,N)
                self.assertGreaterEqual(residual,0)
                self.assertLessEqual(residual,min(m-1,n-1)*z**N)

    def test_dyadic_shell_address_and_variation(self):
        # Exact telescoping on actual positive integer ratios; no float logs.
        for k in range(10):
            a=2**k; b=2*a; ratio=Q(1)
            for n in range(a,b):
                ratio*=Q(n+1,n)
            self.assertEqual(ratio,2)

    def test_rational_eta_tail_for_integer_parameters(self):
        # Test genuine original integer-s eta terms, not an approximation.
        # q is the rational upper bound 1/(1+delta/2).
        for sigma in (1,2,3,4):
            q=Q(2,2+sigma)
            C=1+Q(sigma)/(1-q)
            for k in range(8):
                for N in (2**k,2**k+1,2**k+5):
                    for M in (N,N+1,N+17):
                        tail=sum((Q((-1)**(n-1),n**sigma) for n in range(N,M+1)),Q(0))
                        self.assertLessEqual(abs(tail),C*q**k)


if __name__=='__main__': unittest.main()
