#!/usr/bin/env python3
"""Conditional finite interval E6 photon mode using original 4 Cartan sources.

E32/E33/E21 covectors and K=SU3 trace metric come from #1106/#1241.
The three nonconstant sample profiles are synthetic rational samples,
NOT the actual source 5D bulk/Robin solution. Gauge-energy quadratic
form only; global anomalies, gauge fixing, and stress remain OPEN.
"""
import sympy as s

K=s.diag(1,12,12,4)
Q=s.Matrix([1,s.Rational(1,6),s.Rational(1,6),-s.Rational(1,2)])
PHI=s.Matrix([0,2,1,1])
CHI=s.Matrix([0,2,-2,0])
EW=s.Matrix([-s.Rational(1,2),-1,1,-1])

def interval(profiles, boundary_weight=0, include_ew=True):
    n=len(profiles)
    assert n==3
    h=s.Rational(1,2)
    op=s.zeros(4*n)
    for j,(a,b,t) in enumerate(profiles):
        fields=[a*PHI,b*CHI]+([t*EW] if include_ew else [])
        local=sum((v*v.T for v in fields),s.zeros(4))
        op[4*j:4*j+4,4*j:4*j+4]+=h*local
    for j in range(n-1):
        for sign,node in ((1,j),(-1,j+1)):
            for sign2,node2 in ((1,j),(-1,j+1)):
                op[4*node:4*node+4,4*node2:4*node2+4]+=sign*sign2*K/h
    v=s.Matrix.vstack(*([Q]*n))
    weights=[s.Rational(1,4),s.Rational(1,2),s.Rational(1,4)]
    kinetic=s.diag(*[K*w for w in weights])
    if boundary_weight:
        for j in (0,2):
            kinetic[4*j:4*j+4,4*j:4*j+4]+=boundary_weight*K
    return op,kinetic,v

def check():
    profiles=[
        (s.Rational(9778,10000),s.Rational(9087,10000),s.Rational(3884,10000)),
        (s.Rational(9809,10000),s.Rational(9205,10000),s.Rational(2311,10000)),
        (s.Rational(9778,10000),s.Rational(9087,10000),s.Rational(3884,10000))
    ]
    assert len(set(profiles))==2
    cases=0
    for boundary in (s.Integer(0),s.Rational(1,5),s.Rational(2,3)):
        M,G,v=interval(profiles,boundary)
        assert M==M.T and M.rank()==11 and M*v==s.zeros(12,1)
        assert G.is_positive_definite
        assert (v.T*G*v)[0]==s.Rational(8,3)*(1+2*boundary)
        photon=v/s.sqrt((v.T*G*v)[0])
        assert s.simplify((photon.T*G*photon)[0]-1)==0
        for q in (PHI,CHI,EW): assert (q.T*Q)[0]==0
        cases+=1
    M0,G0,v0=interval(profiles,0,include_ew=False)
    assert M0.rank()==10 and len(M0.nullspace())==2
    M,G,v=interval(profiles,0)
    charged_boundary=s.zeros(12)
    charged_boundary[:4,:4]=Q*Q.T
    assert (M+charged_boundary)*v!=s.zeros(12,1)
    assert (M+charged_boundary).rank()==12
    assert len(s.diag(M,s.zeros(3)).nullspace())==4
    g5,L=s.symbols('g5 L',positive=True)
    assert s.simplify(g5/s.sqrt(L*s.Rational(8,3))-
                      g5*s.sqrt(s.Rational(3,8))/s.sqrt(L))==0
    print('PASS 3/3 positive boundary kinetic configurations, one normalizable photon')
    print('PASS 12x12 nonconstant-profile interval rank 11 and source charge orthogonality')
    print('PASS omitting E21 gives 2 nulls; Q-charged boundary mass kills photon')
    print('PASS additional independent Maxwell adds second null direction')
    print('OPEN source BVP/Robin, dimensionful metric, GS/global anomaly, full QFT stress')

if __name__=='__main__':
    check()
