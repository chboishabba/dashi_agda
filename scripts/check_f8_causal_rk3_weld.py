"""Exact SSPRK3 energy polynomial and original F8 causal-box margins.
Finite tests support, but do not replace, the time-dependent operator bounds.
"""
import math
from fractions import Fraction as F
import sympy as s
import numpy as np


def sqrt_bounds(x, scale=10**12):
    k=math.isqrt((x.numerator*scale**2)//x.denominator)
    return F(k,scale), F(k+1,scale)


def log_bounds(x,n=128):
    assert x>=1
    z=(x-1)/(x+1)
    a=2*sum(z**(2*j+1)/F(2*j+1) for j in range(n))
    return a,a+2*z**(2*n+1)/(F(2*n+1)*(1-z*z))


def causal():
    a,b=sqrt_bounds(F(145));c,d=sqrt_bounds(F(2))
    lo=log_bounds((12+a)/(1+d))[0]-b/12+c
    hi=log_bounds((12+b)/(1+c))[1]-a/12+d
    rl=sqrt_bounds(lo*lo-F(11,12)**2)[0]
    rh=sqrt_bounds(hi*hi-F(11,12)**2)[1]
    Y=F('2.016');R=F('3.01');eps=F('.04');Ybig=F('4.032')
    margins=dict(far_source=F('.1')-eps,
                 top_return=2*Y-F(11,12)-hi,
                 radial_no_hit=R-eps-hi,
                 enlarged_top_no_hit=Ybig+F(1,12)-1-hi)
    assert all(x>0 for x in margins.values())
    # Even the earliest source can reach the small top in the ambient cone;
    # no-hit at that top is NOT certified by this test.
    assert Y<lo
    return dict(span=[float(lo),float(hi)],bulk=[float(rl),float(rh)],
                lower_margins={k:float(v) for k,v in margins.items()})


def exact():
    Q=s.Matrix(4,4,lambda i,j:s.Symbol('q%d%d'%(min(i,j),max(i,j))))
    p=s.Matrix([1,1,s.Rational(1,2),s.Rational(1,6)])
    G=s.Matrix([[1,s.Rational(1,2),s.Rational(1,6)],
                [s.Rational(1,2),s.Rational(1,3),s.Rational(1,6)],
                [s.Rational(1,6),s.Rational(1,6),s.Rational(1,12)]])
    D=s.Matrix(3,3,lambda i,j:-Q[i+1,j]-Q[i,j+1])
    rhs=-sum(G[i,j]*D[i,j] for i in range(3) for j in range(3))-Q[2,2]/12+Q[3,3]/36
    assert s.expand((p.T*Q*p)[0]-Q[0,0]-rhs)==0
    H=G[:2,:2];v=H.inv()*G[:2,2]
    assert H[0,0]>0 and H.det()>0
    assert v==s.Matrix([-s.Rational(1,3),1])
    assert G[2,2]-(G[2,:2]*v)[0]==-s.Rational(1,36)
    k=s.symbols('k');assert s.factor(-s.Rational(1,12)+k/18+k*k/36)==(k-1)*(k+3)/36
    return 4


def samples():
    rng=np.random.default_rng(1547);worst=-np.inf;count=0
    for n in (2,5,12,24):
        for scale in (.1,.5,1.):
            for _ in range(20):
                K=rng.normal(size=(n,n));B=rng.normal(size=(n,n))
                Z=K-K.T-B.T@B;Z*=scale/np.linalg.norm(Z,2)
                R=np.eye(n)+Z+Z@Z/2+Z@Z@Z/6
                gain=np.linalg.norm(R,2);assert gain<=1+1e-13
                worst=max(worst,gain);count+=1
    # Pure imaginary mode beyond the imaginary-axis stability limit.
    Z=np.array([[0.,-2.],[2.,0.]])
    R=np.eye(2)+Z+Z@Z/2+Z@Z@Z/6
    assert np.linalg.norm(R,2)>1
    return dict(cases=count,max_gain=worst)


if __name__=='__main__':
    print(dict(causal=causal(),symbolic=exact(),samples=samples()))
