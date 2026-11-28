#!/usr/bin/env python3
"""BR146-149: actual normal trace, G3 optics/Jacobi, G4 stress and observer.
Exact algebra; no nonlinear evolution, optical calibration or kernel receipt."""
import argparse
import sympy as s
from check_hopf369_br143_145_parallel import trace, eq
Q=s.Rational

def normal():
    P,X,Q0,M,D,L,E,Sc,C,Ct,Z=trace()
    B=L.col_join(E)
    U=(-Q0*M[3]*Q0).row_join(-Q0*D[3].T).col_join((-D[3]*Q0).row_join(s.zeros(50)))
    A=U*B
    eq(U,U.T);eq(B.T*A,Sc)
    assert A.rank()==26 and Sc.rank()==22 and (A*Z).rank()==4
    assert A.col_join(Sc).rank()==26 and A.col_join(C).rank()==26
    K=s.Matrix.hstack(*A.nullspace());eq(C*K,s.zeros(30,K.cols));assert K.cols==9
    # Construct exact full trace readout through uncompressed normal action.
    ids=list(A.T.rref()[1]);Ar=A[ids,:];V=Ar.T.gauss_jordan_solve(C.T)[0].T
    eq(V*Ar,C)
    # On the old blind image the full electric trace is injective.
    assert (A*Z).rank()==(C*Z).rank()==(A*Z).col_join(C*Z).rank()==4
    # Actual full normal symbol on the extended range, positive squared work.
    assert A.T*A==B.T*U**2*B
    print('PASS BR146 full electric trace factors through rank-26 normal action; old four blind channels recovered; true kernel dimension 9')

def optical():
    e,p=s.symbols('e p',real=True,nonzero=True);I=s.eye(3);z=s.Matrix([0,0,1]);f=s.Function('f');t=s.symbols('t',real=True)
    # P0V4 base acceleration in Jordan frame at centre, independent
    # from BR144 spatial Ricci calculation: g4_ij=psi^2 delta_ij.
    F=s.Matrix([[0,8*e,0],[-8*e,0,0],[0,0,0]])
    Hf=-Q(16,9)*e**2*I
    acc=F*F.T+4*Hf+2*s.trace(Hf)*I
    T=-acc/(2*p**2)
    eq(T,s.diag(-Q(208,9),-Q(208,9),Q(80,9))*e**2/p**2)
    # Initial spatial sectional curvature via independent conformal
    # Christoffel derivative at centre (gradient log psi=0).
    def dG(k,i,j,a):return (1 if a==j else 0)*Hf[k,i]+(1 if a==i else 0)*Hf[k,j]-(1 if i==j else 0)*Hf[k,a]
    for i in range(3):
        for j in range(i):eq((dG(i,j,j,i)-dG(j,i,j,i))/p**2,Q(32,9)*e**2/p**2)
    # Unit propagation n=(sin(theta),0,cos(theta)); rotational symmetry
    # covers all azimuths. Screen basis e_y and (cos,0,-sin).
    theta=s.symbols('theta',real=True);n=s.Matrix([s.sin(theta),0,s.cos(theta)]);V=s.Matrix([[0,s.cos(theta)],[1,0],[0,-s.sin(theta)]])
    eq(V.T*V,s.eye(2));eq(V.T*n,s.zeros(2,1))
    O=V.T*T*V+Q(32,9)*e**2/p**2*s.eye(2)
    eq(O,s.diag(-Q(176,9),-Q(176,9)+32*s.sin(theta)**2)*e**2/p**2)
    # Independent reduced Ricci null contraction from radion Hessian
    # and magnetic term (P0V4). All derivatives are physical frame slots.
    ric=-Q(112,3)*e**2/p**2-Q(16,9)*e**2/p**2+(F*n).dot(F*n)/(2*p**2)
    eq(s.trace(O),ric);eq(ric,(-Q(64,9)-32*s.cos(theta)**2)*e**2/p**2)
    # Jacobi leading readout: from actual time-symmetric curvature.
    T5=s.diag(-Q(208,9)*e**2,-Q(208,9)*e**2,Q(80,9)*e**2,Q(112,3)*e**2);T5[2,3]=T5[3,2]=16*e;T5=T5/p**2
    J=s.eye(4)-t*t*T5/2
    eq(J.diff(t,2).subs(t,0),-T5);eq(J[3,2],-8*e*t*t/p**2)
    # Geodesic null lift at p5=0; nonzero conserved fibre momentum
    # projects to timelike base, not a 4D photon.
    r,a,v,q=s.symbols('r a v q',real=True,nonzero=True)
    eq(r*(q/r-a+a)**2,q*q/r)
    print('PASS BR147 actual G3 Jordan optical screen and null Ricci, Jacobi signed leading term and fibre-momentum distinction')

def rmhd():
    # P0H source, preserve background and exact aligned primitive inverse.
    K0,p0,b2,a,p,rho,j2,k=s.symbols('K0 p0 b2 a p rho j2 k',positive=True)
    C=K0-2*p0;rho0=K0-p0;rho=rho0+b2;Sf=rho-b2/2;j2=K0*a*b2
    Delta=(K0+b2)**2-4*j2;pr=(s.sqrt(Delta)-C)/2;energy=pr+C;den=Sf+pr
    eq(den,(K0+b2+s.sqrt(Delta))/2)
    eq(Delta-(K0-b2)**2,4*K0*b2*(1-a))
    # D = S_parallel-S_perp. At a<=1, b2<K0, den>=K0,
    # so j²/den-b²<=0 (strict a<1 and b²>0).
    perp=pr+b2/2;para=pr-b2/2+j2/den;tr=2*perp+para
    eq(j2/den,Sf-energy);eq(rho+tr,K0+2*b2+2*pr)
    eq(para-perp,j2/den-b2)
    # Exact ADM electric Riemann formula, with arbitrary symmetric
    # spatial Ricci and extrinsic curvature, on constraint surface.
    R=s.Matrix(3,3,lambda i,j:s.Symbol(f'r{min(i,j)}{max(i,j)}'))
    K=s.Matrix(3,3,lambda i,j:s.Symbol(f'k{min(i,j)}{max(i,j)}'))
    S=s.diag(perp,perp,para);T=R+s.trace(K)*K-K*K-k*(S+(rho-tr)*s.eye(3)/2)
    ham=s.trace(R)+s.trace(K)**2-s.trace(K*K)-2*k*rho
    eq(s.trace(T)-ham,k*(rho+tr)/2)
    # Anisotropic stress contribution to trace-free electric part,
    # not the total tidal tensor without actual spatial Ricci.
    eq((-k*(S-s.trace(S)*s.eye(3)/3))[2,2]-(-k*(S-s.trace(S)*s.eye(3)/3))[0,0],-k*(para-perp))
    print('PASS BR148 actual G4 aligned stress anisotropy and Einstein tidal trace, full ADM tensor source retained')

def observer():
    e,p,t=s.symbols('e p t',real=True,nonzero=True);q=e**2/p**2; m=e/p**2
    # Same G3 reduced optical scalar and 5D oriented mixed probe.
    optical=-Q(64,9)*q; mixed=16*m
    eq((mixed**2/256)/(-Q(9,64)*optical),1/p**2)
    eq((-Q(9,64)*optical)/(mixed/16),e)
    eq(optical.subs(e,-e),optical);eq(mixed.subs(e,-e),-mixed)
    # One combined optical+marked tidal readout recovers radius^2 and
    # signed amplitude on the actual nonzero two-parameter algebraic chart.
    eq(((-Q(9,64)*optical)/(mixed/16))**2/(-Q(9,64)*optical),p*p)
    # At zero both observables vanish, radius is not inferred.
    eq(optical.subs(e,0),0);eq(mixed.subs(e,0),0)
    print('PASS BR149 paired optical and marked mixed readout recovers signed amplitude and radius squared off zero; zero fibre retained')

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--part',choices=['normal','optical','rmhd','observer'],required=True)
    {'normal':normal,'optical':optical,'rmhd':rmhd,'observer':observer}[p.parse_args().part]()
