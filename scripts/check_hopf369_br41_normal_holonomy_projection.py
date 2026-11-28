#!/usr/bin/env python3
"""BR41b: quantitative two-sided BS11 normal holonomy projection, exact arithmetic.

BS11/13 normal displacement xi and shift U have ZERO endpoint values.
Positive rank-one Gram yields coercive source projection in retained scalar
and vector holonomy channels; not a 5D Einstein curvature-to-metric estimate.
"""
from fractions import Fraction as F
import sympy as s

def project(weight,source):
    assert len(weight)==len(source) and all(w>0 for w in weight)
    gram=sum(weight,F(0))
    coefficient=sum((w*v for w,v in zip(weight,source)),F(0))/gram
    residual=tuple(v-coefficient for v in source)
    projected=sum((w*v for w,v in zip(weight,residual)),F(0))
    assert projected==0
    raw=sum((w*v*v for w,v in zip(weight,source)),F(0))
    error=sum((w*v*v for w,v in zip(weight,residual)),F(0))
    assert error+gram*coefficient*coefficient==raw
    return coefficient,residual,raw,error

def main():
    n,t=s.symbols('n t',real=True)
    l=s.log(2); L=2*l
    b=s.Rational(4,5)*s.cosh(n-l)
    b2=b*b;b4=b2*b2
    I2=s.simplify(s.integrate(b2,(n,0,L)))
    I4=s.simplify(s.integrate(b4,(n,0,L)))
    want2=s.Rational(16,25)*l+s.Rational(3,5)
    want4=s.Rational(192,625)*l+s.Rational(147,250)
    assert s.simplify(I2-want2)==0
    assert s.simplify(I4-want4)==0
    assert b.subs(n,0)==1 and b.subs(n,L)==1 and b.subs(n,l)==s.Rational(4,5)
    # Scalar: xi'= -phi-2 C b²; the exact endpoint constraint
    # C= -int(phi)/(2 int(b²)). Normalized source y=phi/(2b²).
    phi=2*b2*(n-l)
    C=-s.integrate(phi,(n,0,L))/(2*I2)
    assert C==0
    xi=s.integrate(-phi-2*C*b2,(n,0,t))
    assert s.simplify(xi.subs(t,0))==0 and s.simplify(xi.subs(t,L))==0
    # Vector: U'=b^4(A-beta), A = int(b^4 beta)/int(b^4).
    beta=n-l
    A=s.integrate(b4*beta,(n,0,L))/I4
    assert s.simplify(A)==0
    U=s.integrate(b4*(A-beta),(n,0,t))
    assert s.simplify(U.subs(t,0))==0 and s.simplify(U.subs(t,L))==0
    print('PASS exact AK warp b in [4/5,1], two positive holonomy integrals, both endpoint zero gauges')
    # Discrete exact projection gives the constructive mean/orthogonal
    # complement for arbitrary signed sources, including constant modes.
    weights2=[F(16,25),F(4,5),F(1),F(4,5),F(16,25)]
    weights4=[x*x for x in weights2]
    srcs=[tuple(F((i+3)*(k+2)%17-8,7) for i in range(5))
          for k in range(9)]
    for w in (weights2,weights4):
        for src in srcs:
            c,r,raw,error=project(w,src)
            assert error<=raw
            shift=F(13,17)
            cc,rr,_,_=project(w,tuple(x+shift for x in src))
            assert cc==c+shift and rr==r
            # Normal zero-endpoint discrete Poincare:
            # ||xi||_{w,h}^2 <= (max w/min w)*L² ||Dxi||_{w,h}²
            # with L<2, so coefficient <4*(5/4)^4 < 10.
            # Proof uses xi(0)=0 and Cauchy over preceding edges.
            v=[F(0),*r[:3],F(0)];steps=[v[i+1]-v[i] for i in range(4)]
            unweighted_v=sum(x*x for x in v)
            unweighted_d=sum(x*x for x in steps)
            assert unweighted_v<=4*4*unweighted_d
            weighted_v=sum(w[i]*v[i]*v[i] for i in range(5))
            # Edge weight lower estimate using adjacent original carrier.
            low=min(w);high=max(w)
            assert weighted_v<=F(high,low)*16*sum(low*e*e for e in steps)
    print('PASS 18 exact weighted normal projection, residual orthogonality, variance identity')
    print('PASS signed constant-mode invariance and discrete boundary Poincare controls')
    print('Scope: reference normal holonomy, no global variable H^s quotient estimate')

if __name__=='__main__':main()
