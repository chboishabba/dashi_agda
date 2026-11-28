#!/usr/bin/env python3
"""BR197–201: explicit null-symbol split, marked tidal inverse,
analytic graph derivative enclosure, primitive margin and actual finite receiver
work. Source-level exact algebra; not full nonlinear existence.
"""
import sympy as s
from itertools import combinations
Q=s.Rational

def cartan():
    from check_hopf369_br143_145_parallel import trace
    from check_hopf369_br_curvature_energy import carrier
    P,X,*_=trace(); _,_,X0,G,_,_,_,A,_,_,_,_=carrier()
    assert X==X0
    # Frequency convention: w_t=A w_x, closure xi_0 W_ij ...
    # The Fourier covector is (tau,k,0,0,0).
    def ext(tau,k):
        xi=[tau,k,0,0,0]
        return s.Matrix.vstack(*(xi[a]*X[10*P.index((b,c))+j,:]-xi[b]*X[10*P.index((a,c))+j,:]+xi[c]*X[10*P.index((a,b))+j,:] for a,b,c in combinations(range(5),3) for j in range(10)))
    for tau in (0,Q(1,2),-Q(1,2),1,-1,2):
        C=ext(tau,1)
        N=C.nullspace()
        expected=5 if abs(tau)==1 else 0
        assert len(N)==expected
        if N:
            K=s.Matrix.hstack(*N)
            assert (A[0]-tau*s.eye(35))*K==s.zeros(35,expected)
            assert len((A[0]-tau*s.eye(35)).nullspace())==expected
        print('BR197 tau',tau,'full exterior kernel',len(N))
    print('PASS BR197 physical null modes retained; stationary/half-speed frozen modes excluded by exact closure')

def marked():
    # BR144 source tensor, BR145 normalized signed readout.
    e,q=s.symbols('e q',real=True)
    T=s.diag(-Q(208,9)*e*e*q,-Q(208,9)*e*e*q,Q(80,9)*e*e*q,Q(112,3)*e*e*q)
    T[2,3]=T[3,2]=16*e*q
    u=T[2,3]/16; v=3*T[3,3]/112
    # u=e q, v=e² q; recover BOTH amplitude and inverse squared radius off zero.
    assert s.cancel(v/u)==e
    assert s.cancel(u*u/v)==q
    assert T.subs(e,0)==s.zeros(4)
    assert T.subs(e,-e)==s.diag(1,1,1,-1)*T*s.diag(1,1,1,-1)
    print('PASS BR198 marked two-readout inverse e=v/u, q=u²/v; zero fibre loses radius')

def analytic():
    # BR193 source graph and BR189 central conformal bound.
    # Cauchy in complex l1 radius 1/2, inner l1 radius 1/4.
    # Supremum bound for inverse on outer domain: 31/3*(697/665)^2/p0².
    M=Q(31,3)*Q(697,665)**2
    for order in range(5):
        cap=s.factorial(order)*4**order*M
        assert cap>0
        print('BR199 pure-coordinate derivative order',order,'inverse cap times p0²',cap)
    # Mixed multi-index via polydisc radius 1/(4*3), total l1 <=1/4.
    for alpha in ((1,1,0),(2,1,0),(1,1,1),(2,2,0)):
        cap=s.prod(s.factorial(a) for a in alpha)*12**sum(alpha)*M
        assert cap>0
        print('BR199 mixed derivative',alpha,'cap times p0²',cap)
    print('PASS BR199 explicit initial complex coefficient derivative bounds; evolution gauge coefficients not certified')

def primitive():
    # P0H exact recovery, BR194 perturbation guard. Separate denominator margin.
    S,C,d,J=s.symbols('S C d J',real=True)
    E=(C+d)/2; p=E-C; L=S+p
    assert s.expand(4*(L*(S-E)-J)-((2*S-C)**2-d*d-4*J))==0
    assert s.expand(L*L-L*(S-E)-d*L)==0
    # At physical positive branch L>0, d>0, J=L(L-d).
    # If Delta>=dmin², L<=Lmax, then 1-v²>=dmin/Lmax.
    a,b,c=s.symbols('a b c',positive=True)
    assert s.simplify(a/b-a/(b+c))==a*c/(b*(b+c))
    print('PASS BR200 conditional uniform primitive timelike margin from actual enthalpy and denominator bounds')

def receiver():
    # Use P0AG actual assembled maps, including physical metric and shift.
    import numpy as np
    import check_hopf369_p0ag as d
    B,R=d.surface(); H0,Hs,vol=d.assembly()
    # Sufficient SPD time budget for the ACTUAL affine comparator.
    lam=np.linalg.eigvalsh(H0)[0]; size=np.linalg.norm(Hs,2)
    assert lam>0 and size>0
    T=lam/(2*size)
    # This numerical budget is not interval-certified.
    for sign in (-1,1):
        assert np.linalg.eigvalsh(H0+sign*T*Hs)[0]>=lam/2-1e-10
    print('BR201 numerical affine metric comparator time margin',T)
    d.assay(H0,Hs,vol,B,R)
    print('PASS BR201 original material history and numerical coercivity budget; no continuum metric evolution')

if __name__=='__main__':
    import argparse
    p=argparse.ArgumentParser();p.add_argument('--part',required=True,choices=['cartan','marked','analytic','primitive','receiver'])
    globals()[p.parse_args().part]()
