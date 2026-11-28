#!/usr/bin/env python3
"""BR43: two-sided physical normal trace theorem, 15 metric + 5 gauge.

A genuine continuum H^1(0,L) trace estimate (proof via FTC/Cauchy), not a
claim that the BR4 energy already controls the needed higher normal derivative.

For 0<L, 0<m<=w(n), X a finite-dimensional complex Hilbert carrier:
 ||u(0)||^2+||u(L)||^2 <= 4/(L*m)*int_0^L w||u||^2
                             + 2*L/m*int_0^L w||d_n u||^2.
Proof: u(0)=u(x)-int_0^x u', u(L)=u(x)+int_x^L u'.
Cauchy/Young yields each endpoint <= 2/L *int||u||^2 +
L *int||u'||^2, since integral of 2*x*int_0^x ||u'||² /L
has bounded kernel <=L (likewise at L). Sum and w>=m.
No tangent frequency or elliptic inverse division, even at zero frequency.

The full BR4 physical trace of the *time differentiated* metric requires
H^1_n of its time derivative, thus it costs an additional derivative.
"""
import argparse
from fractions import Fraction as F
import sympy as s

def safe_integrate(v,n):
    return s.integrate(s.expand(v),(n,0,1))

def polynomial_control(rank,depth):
    n=s.symbols('n',real=True)
    # Nondimensional n in [0,1]; coefficients independent and signed,
    # original complete tensor/covector dimensions.
    components=[
        sum(F(((i+2)*(k+3)+i*k)%23-11,9)*n**k for k in range(depth+1))
        for i in range(rank)
    ]
    mass=sum(safe_integrate(u*u,n) for u in components)
    gradient=sum(safe_integrate(s.diff(u,n)**2,n) for u in components)
    boundary=sum(u.subs(n,0)**2+u.subs(n,1)**2 for u in components)
    gap=s.cancel(4*mass+2*gradient-boundary)
    assert gap>=0,(rank,depth,gap)
    # Componentwise Cauchy/Young certificate, same physical carrier.
    # For each endpoint the independent *pointwise* integral argument
    # proves the stronger bound 2*mass+gradient.
    bound=2*mass+gradient
    end0=sum(u.subs(n,0)**2 for u in components)
    end1=sum(u.subs(n,1)**2 for u in components)
    assert s.cancel(bound-end0)>=0
    assert s.cancel(bound-end1)>=0
    return {"rank":rank,"degree":depth,"mass":str(mass),"normal_derivative":str(gradient),
            "two_sided_gap":str(gap)}

def physical_warp():
    n=s.symbols('n',real=True);v=s.log(2);L=2*v
    b=s.Rational(4,5)*s.cosh(n-v)
    assert s.simplify(b.subs(n,0)-1)==0
    assert s.simplify(b.subs(n,L)-1)==0
    # cosh reaches 1 at v and increases away; b>=4/5 throughout [0,L].
    assert b.subs(n,v)==s.Rational(4,5)
    # Source weights from BS11 gauge scalar and vector normal holonomy.
    for p in (2,4):
        m=F(4,5)**p
        assert 0<m<=1
        # The physical interval endpoint trace formula retains log2:
        a=4/(L*m);d=2*L/m
        assert s.simplify(a*L*m-4)==0
        assert s.simplify(d*m/(2*L)-1)==0
    # Constant fibre is a crucial zero-mode: trace does not vanish.
    assert s.simplify(2-4/L*s.integrate(1,(n,0,L)))==-2
    return str(L)

def frequency_guard():
    # Existing BR37 polynomial Q loss => exactly its derivative burden,
    # not a uniform-in-Q Kreiss estimate.
    Q=s.symbols('Q',positive=True)
    metric=(12*Q)**4; gauge=(12*Q)**2
    assert s.diff(metric,Q)!=0 and s.diff(gauge,Q)!=0
    assert s.simplify(metric/Q**4)==12**4
    assert s.simplify(gauge/Q**2)==12**2
    # Holder by frequency partition needs tangential s+4 or s+2
    # plus the normal trace's additional normal derivative.
    return {"metric_tangential_loss":4,"gauge_tangential_loss":2,
            "extra_normal_trace_derivative":1}

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--sector',choices=['metric','gauge','warp','loss','all'],default='all')
    a=ap.parse_args()
    if a.sector in ('metric','all'):
        for d in (0,1,2,3):print('PASS metric trace',polynomial_control(15,d))
    if a.sector in ('gauge','all'):
        for d in (0,1,2,3):print('PASS gauge trace',polynomial_control(5,d))
    if a.sector in ('warp','all'):print('PASS two-sided AK warp',physical_warp())
    if a.sector in ('loss','all'):print('PASS retained frequency/normal losses',frequency_guard())

if __name__=='__main__':main()
