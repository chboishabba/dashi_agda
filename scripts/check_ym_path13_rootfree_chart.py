"""Exact rational interval chart on small unit-quaternion contours.
No floats, no radius roots or zero test on a constructive real.
Finite interval verification, not an Agda Cauchy inhabitant.
"""
from fractions import Fraction as F
from math import factorial, comb
import sympy as S

class I:
    def __init__(self, lo, hi=None):
        lo,hi=F(lo),F(lo if hi is None else hi)
        d=2**128
        self.lo=F(lo*d//1,d); self.hi=F(-((-hi*d)//1),d)
        assert self.lo<=self.hi
    def __add__(self,o):
        o=iv(o); return I(self.lo+o.lo,self.hi+o.hi)
    __radd__=__add__
    def __neg__(self):return I(-self.hi,-self.lo)
    def __sub__(self,o):return self+-iv(o)
    def __rsub__(self,o):return iv(o)+-self
    def __mul__(self,o):
        o=iv(o); p=[a*b for a in (self.lo,self.hi) for b in (o.lo,o.hi)];return I(min(p),max(p))
    __rmul__=__mul__
    def __truediv__(self,o):
        o=iv(o);assert o.lo>0;return self*I(1/o.hi,1/o.lo)
    def contains(self,x):return self.lo<=x<=self.hi
    def width(self):return self.hi-self.lo

def iv(x):return x if isinstance(x,I) else I(x)
def horner(cs,x):
    s=I(0)
    for c in reversed(cs):s=s*x+c
    return s

def factorial_series(x,k,n):
    # x in [0,1/4]; alternating terms decrease, next term bounds remainder.
    assert 0<=x.lo<=x.hi<=F(1,4)
    s=horner([F((-1)**j,factorial(2*j+k)) for j in range(n)],x)
    tail=x.hi**n/F(factorial(2*n+k))
    return s+ (I(0,tail) if n%2==0 else I(-tail,0))

def arcsinc(s,n):
    # c_j = binom(2j,j)/(4^j*(2j+1)) <= 1 and positive.
    assert 0<=s<=F(1,4)
    t=sum(F(comb(2*j,j),4**j*(2*j+1))*s**j for j in range(n))
    return I(t,t+s**n/(1-s))

def log_chart(q,n):
    q0,*u=q; s=sum(x*x for x in u)
    assert q0>0 and q0*q0+s==1 and s<=F(1,32)
    L=arcsinc(s,n); return [L*x for x in u], I(s)*L*L

def mul(A,B):return [[sum(A[i][k]*B[k][j] for k in range(3)) for j in range(3)] for i in range(3)]
def polynomial(X,a,b):
    X2=mul(X,X)
    return [[I(int(i==j))+a*X[i][j]+b*X2[i][j] for j in range(3)] for i in range(3)]

def certify(q,n):
    y,r2=log_chart(q,n); w=4*r2
    assert w.hi<=F(1,4)
    cos=factorial_series(r2,0,n); sinc=factorial_series(r2,1,n)
    assert cos.contains(q[0])
    assert all((sinc*y[i]).contains(q[i+1]) for i in range(3))
    a=factorial_series(w,2,n); b=factorial_series(w,3,n)
    h=1-w*b; delta=h*h+w*a*a
    assert delta.lo>=F(529,576)
    x,y0,z=y; X=[[I(0),-2*z,2*y0],[2*z,I(0),-2*x],[-2*y0,2*x,I(0)]]
    D=polynomial(X,a,b); J=polynomial(X,-a/delta,(a*a-h*b)/delta)
    for E in (mul(D,J),mul(J,D)):
        assert all(E[i][j].contains(int(i==j)) for i in range(3) for j in range(3))
        assert max(e.width() for row in E for e in row)<F(1,2**n)
    return max(e.width() for row in mul(J,D) for e in row)

def symbolic():
    x,y,z,a,b=S.symbols('x y z a b'); X=S.Matrix([[0,-z,y],[z,0,-x],[-y,x,0]])
    w=x*x+y*y+z*z; h=1-w*b; d=h*h+w*a*a; u=a*a-h*b
    D=S.eye(3)+a*X+b*X**2; N=d*S.eye(3)-a*X+u*X**2
    for E in (N*D,D*N):assert (E-d*S.eye(3)).applyfunc(S.expand)==S.zeros(3)
    # exp(ad) = I + ad D; same coefficients, no extra scalar family.
    assert (S.eye(3)+X*D-(S.eye(3)+h*X+a*X**2)).applyfunc(S.expand)==S.zeros(3)

if __name__=='__main__':
    symbolic(); count=0
    for t in [(F(0),)*3,(F(1,32),F(0),F(0)),(F(1,40),F(-1,48),F(1,64)),(F(-1,16),F(1,32),F(1,64))]:
        s=sum(x*x for x in t);q=((1-s)/(1+s),*(2*x/(1+s) for x in t))
        for n in (8,12,16,24):certify(q,n);count+=1
    print('PASS symbolic two-sided scaled inverse and Ad identity; %d exact rational contour certificates (exp/log, inverse, radius, width)'%count)
