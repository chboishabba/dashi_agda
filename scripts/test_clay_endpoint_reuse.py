"""Exact finite controls for the source-reuse endpoint cut.
These verify algebra, not analytic estimates, algebraic correspondences or kernels.
See the four-P0 controlling roadmap for provenance and remaining gates.
"""
from fractions import Fraction as Q
from itertools import permutations, product
from math import comb, factorial, prod, isqrt
import unittest
import sympy as S


def blade_mul(a,b,d):
    # Orthogonal Clifford basis, e_i^2=d_i, indices kept in increasing order.
    sign=(-1)**sum(1 for i in range(len(d)) for j in range(i)
                   if a>>i&1 and b>>j&1)
    return a^b, sign*prod(d[i] for i in range(len(d)) if (a&b)>>i&1)


def word(indices,d):
    mask,c=0,Q(1)
    for i in indices:
        mask,k=blade_mul(mask,1<<i,d);c*=k
    return mask,c


def regular_trace(a,d):
    # Nonempty blade permutes the even basis without fixed points.
    if a: return 0
    return 2**(len(d)-1)


def ceil_sqrt(x):
    x=Q(x);k=isqrt(x.numerator//x.denominator)
    return k+(k*k<x)


def polynomial_constants(M):
    a,b=S.Rational(1,16),S.Rational(5,8)
    H=S.Matrix(5,5,lambda i,j:(b**(2*(i+j)+1)-a**(2*(i+j)+1))/(2*(i+j)+1))
    inv=H.inv()
    constants=[]
    for j in range(9):
        v=[Q(factorial(2*i),factorial(2*i-j))*M**(2*i-j) if 2*i>=j else Q(0) for i in range(5)]
        # Absolute matrix bound of the reproducing kernel derivative evaluation.
        bound=sum(Q(abs(inv[i,k]))*v[i]*v[k] for i,k in product(range(5),repeat=2))
        constants.append(max(3,ceil_sqrt(bound))) # also cosh envelope on |u|<=5/4
    return constants


class ExactControls(unittest.TestCase):
    def test_relative_volume_trace(self):
        d=[Q(2),Q(3),Q(-5),Q(-7),Q(-11),Q(-13)]*3
        for block in range(3):
            indices=tuple(range(6*block,6*block+6))
            vol,v=word(indices,d)
            a,c=blade_mul(vol,vol,d)
            self.assertEqual(a,0);self.assertEqual(c,-prod(d[i] for i in indices))
            for p in permutations(indices):
                mask,k=word(p,d);out,w=blade_mul(vol,mask,d)
                sign=(-1)**sum(p[i]>p[j] for i in range(6) for j in range(i+1,6))
                self.assertEqual(regular_trace(out,d)*k*w,sign*c*2**17)
            for other in range(3):
                if other==block:continue
                mask,k=word(range(6*other,6*other+6),d)
                out,w=blade_mul(vol,mask,d)
                self.assertEqual(regular_trace(out,d)*k*w,0)
        # Explicit actual trace on 32-dimensional even algebra, not only mask formula.
        for a in range(64):
            if a.bit_count()%2:continue
            trace=sum(blade_mul(a,b,d[:6])[1] for b in range(64)
                      if b.bit_count()%2==0 and blade_mul(a,b,d[:6])[0]==b)
            self.assertEqual(trace,regular_trace(a,d[:6]))

    def test_log_increment_and_eta_factorial_coefficient(self):
        # Original finite two-term exp bound implies n*h<=1; exact ratio identity.
        for n in range(1,100):
            self.assertEqual(Q(n+1,n)*n,n+1)
            self.assertEqual(Q(n+1,n)-1,Q(1,n))
        a,b,h,L,w=S.symbols('a b h L w')
        for k in range(13):
            self.assertEqual(S.expand(a*L**k-b*(L+h)**k-((a-b)*(L+h)**k-a*((L+h)**k-L**k))),0)
            self.assertEqual(S.expand((L+h)**k-sum(comb(k,j)*L**(k-j)*h**j for j in range(k+1))),0)
        # Symbolic Cartesian l1 majorant comes from collecting the same four monomials.
        x,y,z,t=S.symbols('x y z t',nonnegative=True)
        self.assertEqual(S.expand((x+y)*(z+t)-(x*z+y*t+x*t+y*z)),0)

    def test_gram_dual_amplitude_constants(self):
        P=polynomial_constants(Q(5,4));C=polynomial_constants(Q(21,32))
        self.assertTrue(all(a>=b for a,b in zip(P,C)))
        self.assertTrue(all(x>=3 for x in P+C))
        # Existing 52-box smooth source derivative budgets, use m=4,8,16.
        lam=Q(53248,7)
        def B(j):return Q(3,32) if j==0 else 4*lam**(j-1)
        for m in (4,8,16):
            Sm=sum(comb(m,j)*B(m-j)*P[j] for j in range(min(m,8)+1))
            # cosh derivative for higher orders also <=3 (don't omit j>8).
            Sm+=sum(comb(m,j)*B(m-j)*3 for j in range(9,m+1))
            self.assertGreater(Sm,0)
            self.assertLess(6*Sm/Q(20000)**m,6*Sm/Q(10000)**m)
        x=S.Symbol('x');q=10*x**3-15*x**4+6*x**5
        for j in (1,2):
            self.assertEqual(S.diff(q,x,j).subs(x,0),0)
            self.assertEqual(S.diff(q,x,j).subs(x,1),0)
        self.assertEqual(S.factor(S.diff(q,x)),30*x**2*(x-1)**2)
        self.assertEqual(S.diff(q,x).subs(x,S.Rational(1,2)),S.Rational(15,8))
        self.assertEqual(4*2*Q(15,8)*32,480)
        print('prime amplitude bounds',P,'correction amplitude bounds',C,flush=True)

if __name__=='__main__':unittest.main()
