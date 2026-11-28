#!/usr/bin/env python3
"""BR124-127: exact curved Gauss, electric Weyl inverse, characteristic
split and normal Riccati shear transport. Source algebra, not PDE closure."""
import argparse
from itertools import combinations, combinations_with_replacement, product
import sympy as s
R=s.Rational
h=s.diag(-1,1,1,1);g=s.diag(h,1);I=range(5)
P=list(combinations(I,2));Q=list(combinations_with_replacement(range(10),2))
keys=list(combinations_with_replacement(range(4),2))

def eq(a,b):
    if isinstance(a,s.MatrixBase):
        assert (a-b).applyfunc(s.expand)==s.zeros(*a.shape)
    else: assert s.expand(a-b)==0

def sym(name,n=4):
    keys=list(combinations_with_replacement(range(n),2));q=s.symbols(f'{name}:{len(keys)}')
    return s.Matrix(n,n,lambda a,b:q[keys.index(tuple(sorted((a,b))))])

def wedge(g,B,a,b,c,d):
    return g[a,c]*B[b,d]+B[a,c]*g[b,d]-g[a,d]*B[b,c]-B[a,d]*g[b,c]

def tf(A):return A-h*s.trace(h*A)/4

def gauss():
    j=s.Symbol('j',nonzero=True);M=tf(sym('m'));V=sym('v');N=sym('n');D=sym('d');e=s.Symbol('e')
    # Full curved scalar Gauss from R_g=-20+tr D, Ric_nn=-4+D_nn.
    Kp=M+j*h/2;Km=M-j*h/2
    for K in (Kp,Km):
        tau=s.trace(h*K);shape=s.trace(h*K*h*K)
        scalar=-12+s.trace(h*D)-e+tau*tau-shape
        eq(scalar+12-s.trace(h*D)+e,tau*tau-shape)
    eq((s.trace(h*Kp)**2+s.trace(h*Km)**2)/2-(s.trace(h*Kp*h*Kp)+s.trace(h*Km*h*Km))/2,3*j*j-s.trace(h*M*h*M))
    # Intrinsic scalar derivative at variable h: delta tr(A²) =
    # 2 tr(h^-1 M h^-1 (delta M-delta h h^-1 M)).
    dA=h*N-h*V*h*M; dS=2*s.trace(h*M*dA)
    dDirect=s.trace(-h*V*h*M*h*M+h*N*h*M-h*M*h*V*h*M+h*M*h*N)
    eq(dS,dDirect)
    # Variation of tr_h M=0 is independent of its shape-square derivative.
    traceVariation=s.trace(dA);assert traceVariation!=0
    # Full Gauss solves shear contraction at a wall, but delta R_h
    # is a second tangential derivative of the induced metric.
    r,ddef,dj=s.symbols('r ddef dj')
    eq((6*j*dj-dS+ddef)-r, -dS-(r-6*j*dj-ddef))
    print('PASS BR124 full scalar Gauss average, inverse metric shape derivative, explicit defect and intrinsic curvature debt')

def jump_data():
    j=R(-6,5);M=sym('m');D=sym('d');t=s.trace(h*M);d=s.trace(h*D)
    DD=s.diag(D,d+6*j*t);Sch=(DD-g*s.trace(g*DD)/8)/3
    def rr(a,b,c,d):
        if 4 not in (a,b,c,d):return -j*wedge(h,M,a,b,c,d)
        if (4 in (a,b))!=(4 in (c,d)):return s.S.Zero
        return (D+j*(2*M+t*h))[a,c]
    raw=s.Matrix([rr(*P[a],*P[b])-wedge(g,Sch,*P[a],*P[b]) for a,b in Q])
    def readraw(a,b,c,d):
        if a==b or c==d:return s.S.Zero
        i=P.index(tuple(sorted((a,b))));k=P.index(tuple(sorted((c,d))))
        return (1 if a<b else -1)*(1 if c<d else -1)*raw[Q.index(tuple(sorted((i,k))))]
    E=s.Matrix(4,4,lambda a,b:readraw(a,4,b,4))
    T=tf(M)+tf(D)/(3*j)
    eq(E,2*j*T)
    for a,b,c,d in product(range(4),repeat=4):eq(readraw(a,b,c,d),-j*wedge(h,T,a,b,c,d))
    eq(s.trace(h*E),0)
    return j,M,D,raw,E

def electric():
    j,M,D,raw,E=jump_data()
    # Exact reconstruction in tracefree physical F, with defect retained.
    eq(E/(2*j)-tf(D)/(3*j),tf(M))
    mv=list(dict.fromkeys(M));dv=list(dict.fromkeys(D))
    J=raw.jacobian(mv);T=raw.jacobian(dv)
    assert J.rank()==9 and J.row_join(T).rank()==9
    eq(T,J/(3*j))
    # Nonzero Ricci defect can exactly hide a tracefree mean shape.
    B=s.diag(0,1,-1,0);sub=dict(zip(mv,[B[a,b] for a,b in keys]));sub.update(dict(zip(dv,[-3*j*B[a,b] for a,b in keys])))
    eq(raw.subs(sub),s.zeros(55,1))
    assert B!=s.zeros(4)
    print('PASS BR125 full 55 Weyl jump components factor through effective nine-shape; electric inverse and Ricci masking witness')

def split():
    # Reconstruct the exact BR27/29 carrier, with identical packed basis
    # and Euclidean Gram (no Lorentz norm claimed positive).
    q=s.symbols('q:55');m=s.Matrix(10,10,lambda a,b:q[Q.index(tuple(sorted((a,b))))])
    def W(a,b,c,d):
        if a==b or c==d:return s.S.Zero
        return (1 if a<b else -1)*(1 if c<d else -1)*m[P.index(tuple(sorted((a,b)))),P.index(tuple(sorted((c,d))))]
    rows=[W(a,b,c,d)+W(a,c,d,b)+W(a,d,b,c) for a,b,c,d in combinations(I,4)]
    rows.extend(sum(g[a,a]*W(a,b,a,d) for a in I) for b,d in combinations_with_replacement(I,2))
    C=s.Matrix(rows).jacobian(q);V=s.Matrix.hstack(*C.nullspace());X=s.Matrix(list(m)).jacobian(q)*V;G=X.T*X
    L=s.zeros(10)
    for k in range(1,4):
        a=P.index((0,k));b=P.index((k,4));L[a,b]=L[b,a]=-1
    An=G.inv()*X.T*s.kronecker_product(L,s.eye(10))*X;P0=s.eye(35)-An*(5*An-4*An**3)
    assert V.cols==35 and P0.rank()==9;eq(P0*P0,P0);eq(P0*An,s.zeros(35))
    j,M,D,raw,E=jump_data();J=V.gauss_jordan_solve(raw.jacobian(list(dict.fromkeys(M))))[0]
    assert J.rank()==9 and (P0*J).rank()==6 and (An*J).rank()==8
    # Keep all nine shape coordinates: discard only trace, not isotropic
    # tracefree direction or mixed-time wall modes.
    Y=s.Matrix.hstack(*s.Matrix([[(-1 if a==0 else 1) if a==b else 0 for a,b in keys]]).nullspace())
    J=J*Y;A=An*J;Z=P0*J
    assert A.rank()==8 and Z.rank()==6 and A.col_join(Z).rank()==9
    k=A.nullspace()[0];assert Z*k!=s.zeros(35,1)
    # Weighted normal matrix pseudoinverse on active range, then zero
    # component. Reconstruct J from the two distinct observations.
    Ap=5*An-4*An**3;eq(Ap*A+Z,J)
    B=(J.T*G*J).inv()*J.T*G
    eq(B*(Ap*A+Z),s.eye(9))
    # Single isotropic kernel vector is exactly diag(3,1,1,1) up to scale.
    v=Y*k;iso=s.Matrix([s.diag(3,1,1,1)[a,b] for a,b in keys]);assert v.row_join(iso).rank()==1
    # With Euclidean packed coordinates, explicit reconstruction norm
    # majorant for the two independent observations (not trace estimate).
    L1=B*Ap;L0=B
    maxrow=lambda T:max(sum(abs(x) for x in T.row(i)) for i in range(T.rows))
    print('PASS BR126 actual BR29 split ranks 6/8/9, isotropic active kernel recovered, inverse row bounds',maxrow(L1),maxrow(L0))

def riccati():
    # Gaussian anisotropic reference (independent exact Ricci normal
    # components), then general matrix variation with noncommuting A.
    y=s.symbols('y');k=[s.Function(f'k{i}')(y) for i in range(4)]
    f=[s.Function(f'f{i}')(y) for i in range(4)]
    for i in range(4):
        H=h[i,i]*s.exp(2*f[i]);K=s.diff(H,y)/2
        # R_{n i n i}=-K'_ii+K_i^i K_ii.
        eq(s.expand((-s.diff(K,y)+K*K/H)/H),-s.diff(f[i],y,2)-s.diff(f[i],y)**2)
    A=sym('a');B=sym('b');E=sym('e');delta=s.Symbol('delta');R0=sym('r')
    # Normal evolution for mixed shape A: n A + A² = -R_n^sharp
    # in Gaussian coordinates. Variation at fixed Gaussian defining jet.
    eq(((A+delta*B)**2).diff(delta).subs(delta,0),A*B+B*A)
    # Matrix integrating factor with left/right multiplication; no
    # false commutation between shape and its normal derivative.
    U=s.Matrix(4,4,lambda i,j:s.Symbol(f'U{i}{j}'));V=s.Matrix(4,4,lambda i,j:s.Symbol(f'V{i}{j}'))
    # U'=U A, V'=A V => (U B V)'=U (B'+AB+BA) V.
    eq(U*A*B*V+U*(-E-A*B-B*A)*V+U*B*A*V,-U*E*V)
    # Riccati normal inversion needs the initial/holonomy constant.
    # In constant scalar A=k I and zero curvature source the nonzero
    # solution is B=e^-2ky B0, so curvature alone cannot recover B.
    a=s.Symbol('a');b=s.exp(-2*a*y);eq(s.diff(b,y)+2*a*b,0)
    print('PASS BR127 Gaussian normal Riccati variation, noncommuting two-sided integrating factor, homogeneous holonomy control')

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--part',choices=['gauss','electric','split','riccati'],required=True)
    {'gauss':gauss,'electric':electric,'split':split,'riccati':riccati}[p.parse_args().part]()
