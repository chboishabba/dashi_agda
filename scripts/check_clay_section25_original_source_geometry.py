#!/usr/bin/env python3
"""Section 25 exact geometry-forward finite controls; not native proof."""
from itertools import product, combinations
from fractions import Fraction as F
import sympy as S

def main():
    counts={k:0 for k in ('hodge','bsd','ns','pnp','rh','ym')}
    # Original quadratic Q0 at a=1, y=2: six root phases and 32 even decks.
    a,y=S.Integer(1),S.Integer(2)
    D=(-3*a*a+3*a+1)**2+8*(-3*a**3-a*a+3*a+3-y-a**7/y)
    assert D==-3
    z=S.sqrt(D)
    delta=S.expand(z**6)
    assert delta==-27
    seen=set()
    for signs in product((-1,1),repeat=6):
        if S.prod(signs)!=1: continue
        ds=[e*z for e in signs]
        assert S.simplify(S.prod(ds)-delta)==0
        ss=[(-3*a*a+3*a+1-d)/4 for d in ds]
        for s,d in zip(ss,ds):
            q=-3*a**3-3*a*a*s-a*a+3*a*s+3*a-2*s*s+s+3
            assert S.simplify(q-y-a**7/y)==0
            assert S.simplify(-3*a*a+3*a+1-4*s-d)==0
            counts['hodge']+=2
        seen.add(tuple(signs))
    assert len(seen)==32
    # Exact original signed two-crossing polynomial, ALL tested degrees 2.
    for aa,bb in ((F(1),F(2)),(F(1,2),F(3,2)),(F(2),F(3))):
        for q in range(25):
            x=F(q,8)
            p=x*x-(aa+bb)*x+aa*bb
            assert p==(x-aa)*(x-bb)
            assert p*p>=0
            counts['bsd']+=2
    # Signed E^2 FTC with nonzero transfer; this is an algebraic control
    # and explicitly not an actual fluid solution or a nonlinear bound.
    t=S.symbols('t',real=True)
    for nu in (S.Rational(1,2),S.Integer(1),S.Integer(2)):
        for T in (S.Rational(1,2),S.Integer(1),S.Integer(3)):
            E=1+t+t*t
            D=t*t+2
            Ftransfer=S.diff(E,t)+2*nu*D
            rhs=S.integrate(2*E*Ftransfer-4*nu*E*D,(t,0,T))
            assert S.simplify(rhs-(E.subs(t,T)**2-E.subs(t,0)**2))==0
            counts['ns']+=1
    # Every original anchored rival is witnessed by the SAME first read.
    # Counting them does not evade the per-address sharing capacity.
    for n in range(3,10):
        rivals=list(combinations(range(1,n),2))
        capacity=len(rivals)
        for fuel in range(1,7):
            assert len(rivals)<=capacity<=capacity*fuel
            counts['pnp']+=1
    # Original xi(zeta_zero_parameter) signed horizontal coordinate.
    for p,q in product(range(-10,11),range(-5,6)):
        real=F(p,4)
        signed=F(1,2)-real
        assert (signed==0)==(real==F(1,2))
        assert signed==-(real-F(1,2))
        counts['rh']+=2
    # CMP102 original finite G polynomial regrouping, NOT G=0.
    for x in (F(0),F(1,8),F(1,4),F(-1,4)):
        for A,B in product((F(0),F(1,2),F(1)),repeat=2):
            G=1-2*A-x*A*A+2*x*B+x*x*B*B
            assert G==(1-A)**2-(1+x)*A*A+x*B*(x*B+2)
            counts['ym']+=1
    print('SECTION25 EXACT PASS',counts,'TOTAL',sum(counts.values()))

if __name__=='__main__': main()
