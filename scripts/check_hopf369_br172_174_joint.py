#!/usr/bin/env python3
"""BR172-174: combined selected shell, spectral inverse, zero-shape wall symbol.
Exact finite matrices; not full atomic or periodic nonlinear acceptance."""
import argparse
from itertools import product
import sympy as s
from check_hopf369_br169_171_bound_trace import sigmas, eq
Q=s.Rational

def atomic():
    I=s.eye(3);z=I[:,2];sig=sigmas();a,c,es,ep,l,x=s.symbols('a c es ep l x',real=True);M=s.zeros(8)
    for i in range(3):
        v=z.cross(I[:,i]);B=-s.I*a*sum((v[k]*sig[k] for k in range(3)),s.zeros(2));M[:2,2+2*i:4+2*i]=B;M[2+2*i:4+2*i,:2]=B.H
        for j in range(3):
            v=I[:,i]*z[j]-I[:,j]*z[i];M[2+2*i:4+2*i,2+2*j:4+2*j]=-s.I*c*sum((v[k]*sig[k] for k in range(3)),s.zeros(2))
    eq(M**3,2*(a*a+c*c)*M)
    L=[s.Matrix(3,3,lambda j,k:-s.I*s.LeviCivita(i,j,k)) for i in range(3)]
    SO=s.diag(s.zeros(2),sum((s.kronecker_product(L[i],sig[i]/2) for i in range(3)),s.zeros(6)))
    Jz=s.diag(s.zeros(2),s.kronecker_product(L[2],s.eye(2)))+s.kronecker_product(s.eye(4),sig[2]/2)
    H=M+s.diag(es,es,*([ep]*6))+l*SO
    eq(H,H.H);eq(H*Jz,Jz*H)
    U=s.kronecker_product(s.eye(4),s.I*sig[1]);eq(U*U.conjugate(),-s.eye(8));eq(U*H.conjugate()*U.H,H);eq(U*Jz.conjugate()*U.H,-Jz)
    f=(x-es)*((x-ep+l/2)*(x-ep)-2*c*c-l*l/2)-2*a*a*(x-ep)
    for j in (Q(3,2),Q(1,2),-Q(1,2),-Q(3,2)):
        E=s.Matrix.hstack(*(Jz-j*s.eye(8)).nullspace());R=((E.H*E).inv()*E.H*H*E).applyfunc(s.simplify);eq(E*R,H*E)
        poly=R.charpoly();eq(poly.as_expr().subs(poly.gen,x),f if abs(j)==Q(1,2) else x-ep-l/2)
    print('PASS BR172 combined shell axial action, Kramers antiunitary and exact doubled cubic')

def inverse():
    a,c,es,ep,l,x=s.symbols('a c es ep l x',real=True)
    f=(x-es)*((x-ep+l/2)*(x-ep)-2*c*c-l*l/2)-2*a*a*(x-ep)
    eq(f.subs(x,es),-2*a*a*(es-ep));eq(f.subs(x,ep),-(ep-es)*(2*c*c+l*l/2))
    eq(f.subs({a:-a,c:-c},simultaneous=True),f)
    eq(f.subs(es,ep),(x-ep)*((x-ep+l/2)*(x-ep)-2*(a*a+c*c)-l*l/2))
    # BR170 fixed marked linear observations, independent of eigenvalues.
    sig=sigmas();B=-s.I*a*sig[1];C=-s.I*c*sig[0]
    eq(s.I*s.trace(sig[1]*B)/2,a);eq(s.I*s.trace(sig[0]*C)/2,c)
    print('PASS BR173 spectral inverse off s/p degeneracy, residual norm at degeneracy, signed marked block readout')

def wall():
    from check_hopf369_br_curvature_energy import carrier
    from check_hopf369_br143_145_parallel import trace
    C,V,X,G,Y,H,J,A,B,R,W,m=carrier();P,X2,Q0,M,D,L,E,Sc,T,Tsp,Z=trace();eq(X,X2)
    Dj=s.Matrix.hstack(*(d*X for d in D));ids=list(Dj.T.rref()[1]);Di=D[0][ids,:]*X
    for mu,rank,full,sp in ((Q(1,2),3,5,2),(-Q(1,2),3,5,2),(0,4,4,1)):
        V=s.Matrix.hstack(*(A[0]-mu*s.eye(35)).nullspace());RV=R*V;N=s.Matrix.hstack(*RV.nullspace());assert RV.rank()==rank and N.cols==5
        eq(R*V*N,s.zeros(9,5));assert (T*Di*V*N).rank()==full and (Tsp*Di*V*N).rank()==sp
    # Exact rational direction chart on the reference 1-normal plane.
    u=s.symbols('u',real=True);co=(1-u*u)/(1+u*u);si=2*u/(1+u*u)
    Aw=co*A[0]+si*A[3];Du=(co*D[0]+si*D[3])[ids,:]*X
    w=s.zeros(35,1)
    for i,v in {0:2*u,4:-2*u,8:u*u-1,13:2*(u*u-1),23:-1-u*u,26:-2*(1+u*u)}.items():w[i]=v
    eq(Aw*w,w/2);eq(R*w,s.zeros(9,1));c=Du*w;eq(w.T*G*w,s.Matrix([[24*(1+u*u)**2]]))
    ratio=(c.T*Tsp.T*Tsp*c)[0]/(w.T*G*w)[0]
    eq(ratio,si**2*co**2/12)
    for t in (Q(1,100),Q(1,10),Q(1,2)):
        V=s.Matrix.hstack(*(Aw.subs(u,t)-s.eye(35)/2).nullspace());assert V.cols==8 and (R*V).rank()==7
        eq(R*w.subs(u,t),s.zeros(9,1));assert (Tsp*Du*w).subs(u,t)!=s.zeros(9,1)
    print('PASS BR174 zero-shape wall compatibility: exact tilted half-speed mode and spatial trace ratio sin^2 cos^2/12')

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--part',choices=['atomic','inverse','wall'],required=True)
    {'atomic':atomic,'inverse':inverse,'wall':wall}[p.parse_args().part]()
