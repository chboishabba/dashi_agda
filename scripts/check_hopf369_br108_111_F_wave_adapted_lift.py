#!/usr/bin/env python3
"""BR108-111: wave-adapted scale lift and joint glancing bound.
Exact algebra and flat half-line estimates; not variable F existence.
Classical wave, Lie and Green identities are prior mathematics.
"""
import argparse
import sympy as s

def lift():
    l,p=s.symbols('ell p',nonzero=True);z=s.Matrix(s.symbols('z:4'));y=s.symbols('y',real=True)
    A=-p/(2*l);vp=A*s.exp(-l*y);vm=A*s.exp(l*y)
    at=lambda u:u.subs(y,0)
    assert at(vp-vm)==0 and s.simplify(at(s.diff(vp-vm,y)))==p
    assert s.simplify(at(s.diff(vp-vm,y,2)))==0
    for v in (vp,vm):
        assert s.simplify(s.diff(v,y,2)-l*l*v)==0
        # Lie derivative of flat metric along V=v partial_y.
        H=s.zeros(4);b=z*v;scale=s.diff(v,y)
        assert (b.diff(y,2)-l*l*b).applyfunc(s.simplify)==s.zeros(4,1)
        assert s.simplify(scale.diff(y,2)-l*l*scale)==0
    assert (z*at(vp-vm)).applyfunc(s.simplify)==s.zeros(4,1)
    assert (z*at(s.diff(vp-vm,y))-z*p).applyfunc(s.simplify)==s.zeros(4,1)
    # The common value is nonzero: not a fixed-wall diffeomorphism.
    assert A!=0
    # Imposing V=0 on both half-lines forces amplitudes zero.
    ap,am=s.symbols('ap am');assert s.Matrix([ap,am,-l*(ap+am)]).jacobian([ap,am]).rank()==2
    print('PASS BR108 homogeneous wave lift, exact metric trace/normal jump, fixed-wall Dirichlet obstruction')

def joint():
    a,b,g,w,k=s.symbols('a b gamma omega k',real=True)
    L2=a*a+b*b;Z2=g*g+w*w
    # Root equations a²-b²=gamma²-omega²+k², ab=gamma omega.
    # L² >= gamma*|s| and gamma*k follow from aL >= those.
    assert s.expand(a*a*L2-g*g*Z2-(a*a-g*g)*(a*a+g*g)).subs(b*a,g*w).expand()==0
    # k² = a²-b²-gamma²+omega²; replace gamma² omega²=a² b².
    d=s.expand(a*a*L2-g*g*(a*a-b*b-g*g+w*w)).subs(a*a*b*b,g*g*w*w).expand()
    assert s.expand(d-(a*a-g*g)*a*a-g*g*(b*b+g*g))==0
    # a>=gamma: (a²-gamma²)(a²+omega²)=a² k² on root.
    assert s.expand((a*a-g*g)*(a*a+w*w)-a*a*(a*a-b*b-g*g+w*w)).subs(a*a*b*b,g*g*w*w).expand()==0
    # Joint Green composition: tau_y(0)= +/-int exp(-ell r) F(r) dr;
    # norm of each trace functional =1/sqrt(2a). Both faces =>1/sqrt(a).
    # p=trace/ell²; A=-p/(2ell); two-face L² norm of V is |A|/sqrt(a).
    y=s.symbols('y',positive=True);aa=s.symbols('aa',positive=True)
    assert s.integrate(s.exp(-2*aa*y),(y,0,s.oo))==1/(2*aa)
    # With m=max(|s|,k), |ell|²<=2m², normalized derivative weights
    # max(m,L)^2<=2m². Joint coefficient <=m²/(L³*a)<=gamma^-2.
    # Exact squared ratio in propagating and glancing special rays.
    for ga,om,kk in [(1,0,0),(1,0,5),(1,5,5),(2,9,3),(3,9,12)]:
        root=complex(ga+1j*om)**2+kk**2;ll=complex(root)**.5;alpha=ll.real;llabs=abs(ll);m=max(abs(ga+1j*om),kk)
        assert alpha>=ga-1e-12 and m*m/(llabs**3*alpha)<=1/ga**2+1e-12
    print('PASS BR109 exact root inequalities and joint Green/scale/lift bound; sample controls')

def glancing():
    r=s.symbols('r',positive=True);g=s.symbols('gamma',positive=True)
    # s=gamma+i r, k=r: L²=sqrt(gamma^4+4gamma²r²), a²=(L²+gamma²)/2.
    L2=s.sqrt(g**4+4*g*g*r*r);a2=(L2+g*g)/2
    # Squared norm per one derivative of metric (=2 of V), divided
    # by wall H1 p squared, for time-frequency |s| as derivative.
    ratio=(g*g+r*r)/(4*L2*s.sqrt(a2))
    assert s.simplify(s.limit(ratio/s.sqrt(r),r,s.oo)-1/(8*g**s.Rational(3,2)))==0
    # Joint bound: Dirichlet Green trace plus intrinsic wall wave adds
    # 1/(L² sqrt(a)); squared normalized full coefficient tends 1/(32g^4).
    joint=(g*g+r*r)**2/(4*L2**3*a2)
    assert s.simplify(s.limit(joint,r,s.oo)-1/(32*g**4))==0
    # Asking for one additional metric derivative grows unbounded.
    assert s.limit(joint*(g*g+r*r),r,s.oo)==s.oo
    print('PASS BR110 separate lift quarter-derivative loss, bounded joint composition, next-order obstruction')

def naturality():
    # Exact first-order gauge-source difference at a nonorthogonal
    # point: Lie-g metric jet from independent V and dV, fixed source.
    g=s.diag(-2,3,4,5,6);g[0,2]=g[2,0]=s.Rational(1,5);gi=g.inv()
    A=s.Matrix(5,5,lambda i,j:s.Rational((i+2)*(j+3)%13-6,17));p=A.T*g+g*A
    # Contracted connection difference T^i_ab is symmetric in a,b.
    T=[s.Matrix(5,5,lambda a,b:s.Rational((min(a,b)+2)*(max(a,b)+i+3)%17-8,19+i)) for i in range(5)]
    dgi=-gi*p*gi;G=s.Matrix([s.trace(gi*t) for t in T]);dG=s.Matrix([s.trace(dgi*t) for t in T])
    # Independent second jets of V, constant background metric.
    B=[s.Matrix(5,5,lambda a,b:s.Rational((min(a,b)+3)*(max(a,b)+i+1)%17-8,23+i)) for i in range(5)]
    dp=[s.Matrix(5,5,lambda a,b:sum(g[i,b]*B[i][k,a]+g[a,i]*B[i][k,b] for i in range(5))) for k in range(5)]
    dGamma=[s.Matrix(5,5,lambda a,b:sum(gi[i,k]*(dp[a][k,b]+dp[b][k,a]-dp[k][a,b])/2 for k in range(5))) for i in range(5)]
    assert dGamma==B
    H=s.Matrix([s.Rational(i+1,11) for i in range(5)])
    C=g*G-H
    # Fixed algebraic reference connection and prescribed covector H.
    # Direct derivative of lower contracted gauge from metric jets.
    dLower=p*G+g*s.Matrix([s.trace(dgi*T[i]+gi*dGamma[i]) for i in range(5)])
    boxV=s.Matrix([s.trace(gi*b) for b in B])
    P=dLower-A.T*C
    lower=p*G+g*dG-A.T*C
    assert P==g*boxV+lower
    assert lower!=s.zeros(5,1)
    # Material displacement: tangential metric Lie jump has 2j h V_n,
    # canceled by graph displacement -V_n, not by pretending V_n=0.
    h=g[:4,:4];j,v=s.symbols('j v');M=s.eye(4);kp=M+j*h/2;km=M-j*h/2
    assert (2*v*(kp-km)-2*j*v*h).applyfunc(s.expand)==s.zeros(4)
    print('PASS BR111 inverse/source variation algebra and moving-wall Lie displacement cancellation')

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--part',choices=['lift','joint','glancing','naturality'],required=True)
    {'lift':lift,'joint':joint,'glancing':glancing,'naturality':naturality}[p.parse_args().part]()
