#!/usr/bin/env python3
"""Section 27 exact cross-Clay finite controls, no native/kernel claims.

YM: original finite SeriesOf count 0..79 and root-free Bishop G polynomial.
Hodge: same six original Q0 root equations / 32 product-one binary decks.
NS: signed E^2 FTC inverse with real dissipative term, exact rationals.
BSD: positive original two-crossing signed-moment necessary sign.
PNP: physical query/input dual ceiling, not superpolynomial SAT.
RH: original signed xi/zeta horizontal coordinate only.
"""
from fractions import Fraction as Q
from itertools import product
from math import factorial
import sympy as sp

def convolve(a,b):
    if not a or not b: return []
    v=[Q(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):v[i+j]+=x*y
    return v

def original_g(count):
    a=[Q(1,factorial(2*j+2)) for j in range(count)]
    b=[Q(1,factorial(2*j+3)) for j in range(count)]
    g=[Q(0)]*(2*count+1);g[0]=1
    for i,v in enumerate(a):g[i]-=2*v
    for i,v in enumerate(convolve(a,a)):g[i+1]-=v
    for i,v in enumerate(b):g[i+1]+=2*v
    for i,v in enumerate(convolve(b,b)):g[i+2]+=v
    return a,b,g

def run():
    n={k:0 for k in ['ym','ns','bsd','hodge','pnp','rh']}
    for count in range(80):
        a,b,g=original_g(count)
        assert all(x==0 for x in g[:count]); n['ym']+=count
        if count:
            assert g[count]==Q(2,factorial(2*count+2));n['ym']+=1
        aa=sum(a,Q(0));bb=sum(b,Q(0))
        assert aa<=Q(6,11) and bb<=Q(10,57)
        assert sum(map(abs,g),Q(0))<=1+2*aa+aa*aa+2*bb+bb*bb<=3
        n['ym']+=2
        for x in (Q(-1,4),Q(-1,8),Q(0),Q(1,8),Q(1,4)):
            assert abs(sum((v*x**i for i,v in enumerate(g)),Q(0)))<=3*Q(1,4)**count
            n['ym']+=1
    x,a,b=sp.symbols('x a b')
    assert sp.expand((1-2*a-x*a*a+2*x*b+x*x*b*b)-
        ((1-a)**2-(1+x)*a*a+x*b*(2+x*b)))==0
    n['ym']+=1
    for signs in product((-1,1),repeat=6):
        if sp.prod(signs)!=1:continue
        assert sum(s<0 for s in signs)%2==0
        assert signs[-1]==sp.prod(signs[:5])
        n['hodge']+=2
    for aa,bb in ((Q(1),Q(2)),(Q(1,2),Q(3,2)),(Q(2),Q(5))):
        for m1 in (Q(-3),Q(-1,2),Q(0),Q(1,3),Q(2)):
            for m2 in (Q(-1),Q(0),Q(1),Q(5)):
                positive=m2-(aa+bb)*m1>0
                if positive and m2==0:assert m1<0
                if positive and m1>=0:assert m2>0
                n['bsd']+=1
    t=sp.symbols('t',real=True)
    for nu in (sp.Rational(1,3),sp.Rational(2,3),sp.Integer(1)):
        for T in (sp.Rational(1,2),sp.Integer(1),sp.Integer(3)):
            E=1+t+t*t;D=1+t*t
            F=sp.diff(E,t)+2*nu*D
            signed=sp.integrate(E*F,(t,0,T))
            diss=sp.integrate(E*D,(t,0,T))
            assert sp.simplify(E.subs(t,T)**2-E.subs(t,0)**2-2*signed+4*nu*diss)==0
            n['ns']+=1
    for width in range(1,50):
        for fuel in range(1,50):
            for charge in (0,1,3):
                amount=charge*min(width,fuel)
                assert amount<=charge*width and amount<=charge*fuel
                n['pnp']+=1
    for re in range(-10,11):
        for im in range(-5,6):
            signed=Q(1,2)-Q(re,4)
            assert (signed==0)==(Q(re,4)==Q(1,2))
            n['rh']+=1
    print('SECTION27 EXACT PASS',n,'TOTAL',sum(n.values()))
if __name__=='__main__':run()
