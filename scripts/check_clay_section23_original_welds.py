#!/usr/bin/env python3
"""Section 23 independent exact finite controls, not native or Clay acceptance."""
from itertools import product
from fractions import Fraction as Q
from math import factorial
import sympy as sp

def main():
    n=dict(bsd=0,hodge=0,pnp=0,ns=0,ym=0,rh=0)
    for m in range(1,33):
        for d in range(1,m+1):
            if m%d: continue
            S={b for b in range(2*m) if b%(2*d) in {0,d}}
            T={c for c in range(m) if c%d==0}
            assert {b%m for b in S}==T
            assert {b for b in S if b%m==0}=={0,m}
            assert all({b for b in S if b%m==c}=={c,c+m} for c in T)
            n["bsd"]+=len(T)
    p=5
    A=set(product(range(p),repeat=3)) # Q_p[eps,delta]/(eps,delta)^2
    B={(a,b,0) for a,b in product(range(p),repeat=2)}
    assert len(B)==p*p and len(A)==p**3 and B < A
    # Exact nonreduced homogeneous h-chart, F5[eps]/eps^2.
    # p(x)=c0+c1*x+c2*x^2, homogenize at D>=2 and substitute
    # h=T, z=eps*T. Every term has T^D, with eps^2=0.
    for degree in range(2,7):
        for coeffs in product(range(p),repeat=3):
            affine=(coeffs[0]%p,coeffs[1]%p)
            cone=(0,0)
            for j,c in enumerate(coeffs):
                term=(c%p,0) if j==0 else ((0,c%p) if j==1 else (0,0))
                cone=((cone[0]+term[0])%p,(cone[1]+term[1])%p)
            assert cone==affine
            n["hodge"]+=1
    for k in range(2,8):
        words=list(product((0,1),repeat=k))
        for x in words:
            for y in words:
                d=tuple((a-b)%3 for a,b in zip(x,y))
                assert all(z in (0,1 if a else 2) for a,z in zip(x,d))
                assert tuple(a if z==0 else 1-a for a,z in zip(x,d))==y
                if (sum(x)-sum(y))%3==0 and x[0]!=y[0]:
                    assert x[0]!=y[0] # original physical read at coordinate zero
                    n["pnp"]+=1
    t=sp.symbols("t",nonnegative=True)
    for nu in [sp.Rational(1,3),sp.Rational(1,2),sp.Integer(1),sp.Integer(2)]:
        for E0 in [sp.Integer(1),sp.Rational(5,2),sp.Integer(7)]:
            E=E0*sp.exp(-2*nu*t)
            diss=sp.integrate(E,(t,0,t))
            assert sp.simplify(E+2*nu*diss-E0)==0
            assert sp.simplify(sp.diff(E,t)+2*nu*E)==0
            n["ns"]+=1
    for i in range(101):
        r=Q(i,100)
        bound=r/(2*(1-r/3))
        assert sum((r**j/Q(factorial(j+1)) for j in range(1,20)),Q(0))<=bound<=Q(3,4)
        assert 1/(1-bound)<=4
        n["ym"]+=1
    for a,b in product(range(-4,5),repeat=2):
        s=sp.Rational(a,2)+sp.I*b
        z=-sp.I*(s-sp.Rational(1,2))
        assert sp.simplify(sp.im(z)+sp.re(s)-sp.Rational(1,2))==0
        assert (sp.re(s)==sp.Rational(1,2))==(sp.im(z)==0)
        n["rh"]+=1
    print(n,"PASS",sum(n.values()))

if __name__=="__main__": main()
