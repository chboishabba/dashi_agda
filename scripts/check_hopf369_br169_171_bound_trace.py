#!/usr/bin/env python3
"""BR169-171: actual initial KK Pauli projection and compatible grazing trace.
Selected leading Pauli model and flat bulk symbol, not coupled evolution.
"""
import argparse
from itertools import product
import sympy as s
from check_hopf369_br165_168_parallel import gamma
Q=s.Rational

def eq(a,b):
    if isinstance(a,s.MatrixBase): assert (a-b).applyfunc(s.simplify)==s.zeros(*a.shape)
    else: assert s.simplify(a-b)==0

def sigmas():
    return [s.Matrix([[0,1],[1,0]]),s.Matrix([[0,-s.I],[s.I,0]]),s.diag(1,-1)]

def pauli():
    g,_=gamma();sig=sigmas();I=s.eye(2);b=s.Matrix(s.symbols('b:3',real=True));db=s.Matrix(3,3,lambda i,j:s.Symbol(f'd{i}{j}',real=True))
    Bs=[s.I*g[0]*g[4]*g[i]*g[j] for i,j in ((2,3),(3,1),(1,2))]
    for i in range(3):
        eq((-g[0]*g[i+1])[:2,2:],-s.I*sig[i]);eq(Bs[i][:2,2:],-sig[i])
    sb=sum((b[i]*sig[i] for i in range(3)),s.zeros(2));eq(sb**2,b.dot(b)*I)
    # Coefficients of momentum and its commutator with multiplication by b.
    for j in range(3):
        v=b.cross(s.eye(3)[:,j]);eq(s.I*(sig[j]*sb-sb*sig[j]),2*sum((v[k]*sig[k] for k in range(3)),s.zeros(2)))
    curl=s.Matrix([db[2,1]-db[1,2],db[0,2]-db[2,0],db[1,0]-db[0,1]])
    eq(sum((sig[i]*sig[j]*db[j,i] for i,j in product(range(3),repeat=2)),s.zeros(2)),s.trace(db)*I+s.I*sum((curl[k]*sig[k] for k in range(3)),s.zeros(2)))
    x,y,z=s.symbols('x y z',real=True);X=(x,y,z);r2=x*x+y*y+z*z
    B=8*s.Matrix([2*x*z-2*y,2*x+2*y*z,1-x*x-y*y+z*z])/(1+r2)**3
    eq(sum(s.diff(B[i],X[i]) for i in range(3)),0)
    print('PASS BR169 actual mass grading, differential Pauli square and original divergence-free linear Hopf source')

def shell():
    r,lam,m=s.symbols('r lam m',positive=True);eps=s.symbols('eps',real=True);D=1+r*r;C2=lam**3/(32*s.pi);z=s.Matrix([0,0,1]);I=s.eye(3)
    n=s.Matrix(s.symbols('n:3',real=True));ns=list(n)
    def avg(f):
        if isinstance(f,s.MatrixBase):return f.applyfunc(avg)
        ans=0
        for powers,c in s.Poly(s.expand(f),*ns).terms():
            if any(p%2 for p in powers):continue
            ans+=c*s.prod(s.factorial2(p-1) for p in powers)/s.factorial2(sum(powers)+1)
        return s.simplify(ans)
    # Original b=eps B/4 to first order in eps; split parity.
    be=2*eps*((1-r*r)*z+2*r*r*n[2]*n)/D**3
    bo=4*eps*r*z.cross(n)/D**3
    for i,j in product(range(3),repeat=2):
        v=I[:,i]*z[j]-I[:,j]*z[i]
        eq(avg((be+bo).cross(r*(n[i]*I[:,j]-n[j]*I[:,i]))),4*eps*r*r*v/(3*D**3))
    for j in range(3):
        v=z.cross(I[:,j]);grad=lam*(2-lam*r)*I[:,j]+lam*lam*r*n[j]*n
        eq(avg((be+bo).cross(grad)),4*eps*lam*(3-r*r-lam*r)*v/(3*D**3))
    # Both 2s/2p radial normalizations, and integration by parts gives
    # a positive integral for the otherwise signed s-p radial coefficient.
    eq(4*s.pi*C2*s.integrate(r*r*(2-lam*r)**2*s.exp(-lam*r),(r,0,s.oo)),1)
    eq(4*s.pi*C2*lam**2/3*s.integrate(r**4*s.exp(-lam*r),(r,0,s.oo)),1)
    eq(s.diff(r**3*s.exp(-lam*r)/D**2,r),r*r*s.exp(-lam*r)*(3-r*r-lam*r-lam*r**3)/D**3)
    a,c=s.symbols('a c',real=True);sig=sigmas();H=s.zeros(8)
    for i in range(3):
        v=z.cross(I[:,i]);B=-s.I*a*sum((v[k]*sig[k] for k in range(3)),s.zeros(2));H[:2,2+2*i:4+2*i]=B;H[2+2*i:4+2*i,:2]=B.conjugate().T
        for j in range(3):
            v=I[:,i]*z[j]-I[:,j]*z[i];H[2+2*i:4+2*i,2+2*j:4+2*j]=-s.I*c*sum((v[k]*sig[k] for k in range(3)),s.zeros(2))
    eq(H,H.conjugate().T);E=s.symbols('E');eq(H.charpoly(E).as_expr(),E**4*(E**2-2*a*a-2*c*c)**2)
    eq(H**3,2*(a*a+c*c)*H);assert H.rank()==4
    print('PASS BR170 full 2s+2p spin-orbital leading Hopf matrix, rank four and signed paired eigenvalues')

def grazing():
    from check_hopf369_br143_145_parallel import trace
    P,X,Q0,M,D,L,E,Sc,T,Tsp,Z=trace();G=X.T*X;A=G.inv()*X.T*M[0]*X
    Dj=s.Matrix.hstack(*(d*X for d in D));ids=list(Dj.T.rref()[1]);Di=D[0][ids,:]*X;K=-D[0][ids,:]*L
    # These are actual constraint images of projected Weyl eigenvectors,
    # not independent incompatible residual first jets.
    for mu,d,rr,rt in ((Q(1,2),8,8,2),(-Q(1,2),8,8,2),(0,9,8,1),(1,5,0,0),(-1,5,0,0)):
        V=s.Matrix.hstack(*(A-mu*s.eye(35)).nullspace());assert V.cols==d
        C=Di*V;eq(K*C,mu*C);assert (T*C).rank()==rr and (Tsp*C).rank()==rt
    # Exact square-root phase bound for |ell|<=sqrt(k), k>=1:
    # sqrt(k^2+ell^2)-k=ell^2/(sqrt(k^2+ell^2)+k)<=1/2.
    k,l=s.symbols('k l',positive=True);eq((s.sqrt(k*k+l*l)-k)*(s.sqrt(k*k+l*l)+k),l*l)
    print('PASS BR171 actual compatible tangential half-speed modes have spatial electric trace rank two (both signs)')

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--part',choices=['pauli','shell','grazing'],required=True)
    {'pauli':pauli,'shell':shell,'grazing':grazing}[p.parse_args().part]()
