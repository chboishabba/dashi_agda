"""Finite exact controls for original imaginary-axis factorial convolution.
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

if __name__=='__main__': unittest.main()
