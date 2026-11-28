#!/usr/bin/env python3
"""BR81: EXISTING P0AK/BN exact AdS5 reference -> static/dynamic BIDI split.

Consumes P0AK full warped Einstein + pure-tension pressure/lapse;
P0BL/BM/BN scalar R(h)=-12; BR79 Hamiltonian/BR71 physical wall.

Reference 4D time-symmetric spatial h=dn²+b(n)² gamma_H3,
gamma_H3 curvature -h0², b=(4/5)cosh(n-log2),
h0=4/5, L=2log2; N=b(n) N0, N0=(h0 z)^-1
in H3 upper half-space. Exact 5D vacuum static equations:
  Ric(h)=-3h,  Hess_h N = N h,  Delta_h N=4N,
  Ric(g5)=-4g5,  R(h)=-12.
N is positive on z>0, and both physical wall Israel jump
j=b'(0)-b'(L)=-6/5, fixed pure tension kappa5² T=-3j.
This is ALREADY P0AK: BR81 only joins its original source geometry
to the BN initial-data constraint and BR78 vacuum tension Ward.

For a NONZERO BN Hopf scalar metric h with R(h)=-12,
K_init=0 makes a valid vacuum HAMILTONIAN/MOMENTUM initial datum,
but it does not prove the static lapse equation
  Hess_h N = N(Ric_h+4h).
Dynamic route requires the full hyperbolic evolution (BR71/72,
BR80, BR29, etc). Static route must solve a distinct overdetermined
tensor equation and its boundary compatibility; no promotion from
a scalar equation.

--part reference|lapse|junction|refusal
"""
import argparse
import sympy as s

def data():
    n,z=s.symbols('n z',real=True,positive=True)
    h0=s.Rational(4,5)
    L=2*s.log(2)
    b=h0*s.cosh(n-s.log(2))
    bp=s.diff(b,n);bpp=s.diff(b,n,2)
    N0=1/(h0*z)
    N=b*N0
    return n,z,h0,L,b,bp,bpp,N0,N

def reference():
    n,z,h0,L,b,bp,bpp,N0,N=data()
    assert s.simplify(bpp-b)==0
    assert s.simplify(bp**2-b**2+h0**2)==0
    assert s.simplify(b.subs(n,0)-1)==0
    assert s.simplify(b.subs(n,L)-1)==0
    # Actual scalar curvature of 1+3 warped spatial h,
    # with H3 Ric=-2 h0² gamma.
    R4=-6*h0**2/b**2-6*bpp/b-6*bp**2/b**2
    assert s.simplify(R4+12)==0
    ricNN=-3*bpp/b
    ricTan=-2*h0**2-b*bpp-2*bp*bp # multiple of gamma_H3
    assert s.simplify(ricNN+3)==0
    assert s.simplify(ricTan+3*b*b)==0
    print('PASS BR81 ORIGINAL P0AK warp spatial scalar R=-12 and Ric_h=-3h')

def lapse():
    n,z,h0,L,b,bp,bpp,N0,N=data()
    # Three spatial H3 base coordinates: gamma=h0^-2 z^-2 I.
    # N0=1/(h0 z) obeys Hess_gamma N0=h0² N0 gamma,
    # checked independently in z and x base directions.
    d=s.diff(N0,z)
    gamma=1/(h0*h0*z*z)
    # Christoffel gamma^z_zz=-1/z, gamma^z_xx=+1/z.
    HessZ=s.diff(N0,z,2)+s.diff(N0,z)/z
    HessX=-s.diff(N0,z)/z
    assert s.simplify(HessZ-h0*h0*N0*gamma)==0
    assert s.simplify(HessX-h0*h0*N0*gamma)==0
    # Warped 4D Hessian: nn=N'', nA=0,
    # AB=b*Hess_gamma N0 +b b' gamma_AB*N'
    hessNN=s.diff(N,n,2)
    hessTang=b*h0*h0*N0+b*bp*s.diff(N,n)
    assert s.simplify(hessNN-N)==0
    assert s.simplify(hessTang-N*b*b)==0
    assert s.simplify((hessNN+3*hessTang/(b*b))/N-4)==0
    print('PASS BR81 original P0AK positive static lapse Hess_h N=Nh, trace Delta N=4N')

def junction():
    n,z,h0,L,b,bp,bpp,N0,N=data()
    j=s.simplify(bp.subs(n,0)-bp.subs(n,L))
    assert j==-s.Rational(6,5)
    kappa=s.Integer(6)
    tension=-3*j/kappa
    assert tension==s.Rational(3,5)
    # Four timelike-wall tangent principal curvatures all use b'/b,
    # including time: the correct lapse jump is [partial_n log N]=j.
    lapseJump=s.simplify((s.diff(N,n)/N).subs(n,0)
                          -(s.diff(N,n)/N).subs(n,L))
    assert lapseJump==j
    assert s.simplify(j+kappa*tension/3)==0
    assert s.simplify(s.diff(tension,z))==0
    print('PASS BR81 time-direction lapse + three spatial Israel directions, fixed tension Ward')

def refusal():
    n,z,h0,L,b,bp,bpp,N0,N=data()
    # SAME BN spatial h (R=-12), but choose N_bad=b independent
    # of H3. Positive lapse alone does NOT imply static Einstein.
    # Tangential warped Hess N_bad=b*(b')² gamma,
    # while static equation requires N_bad b² gamma.
    Nbad=b
    tang=s.simplify(b*bp*bp-Nbad*b*b)
    assert s.simplify(tang+h0*h0*b)==0
    assert tang!=0
    # The time-symmetric K=0 initial ADM constraints still hold:
    R=-12 and momentum=0, so a dynamic development is distinct
    # from a lapse-static Einstein metric.
    scalar=-6*h0**2/b**2-6*bpp/b-6*bp**2/b**2
    assert s.simplify(scalar+12)==0
    print('PASS BR81 refusal: BN scalar constraint does NOT force static Hessian lapse or full 5D evolution')

def main():
    p=argparse.ArgumentParser()
    p.add_argument('--part',choices=('reference','lapse','junction','refusal'),default='reference')
    x=p.parse_args()
    {'reference':reference,'lapse':lapse,'junction':junction,'refusal':refusal}[x.part]()
if __name__=='__main__':main()
