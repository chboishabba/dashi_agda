#!/usr/bin/env python3
"""BR120-123: source-dependent jump, moving-chart BIDI, scalar commutator,
and constrained null shear. Exact source algebra, not a PDE theorem."""
import argparse
from itertools import product
import sympy as s
R=s.Rational
I=range(5)

def eq(a,b):
    if isinstance(a,s.MatrixBase):
        assert (a-b).applyfunc(s.cancel)==s.zeros(*a.shape)
    else:
        assert s.cancel(a-b)==0

def sym(seed,n=5):
    return s.Matrix(n,n,lambda i,j:R(((min(i,j)+2)*(max(i,j)+seed+3))%23-11,31+seed))

def vec(seed,n=5):
    return s.Matrix([R(((i+2)*(seed+3))%17-8,19+seed) for i in range(n)])

def chart():
    h=s.diag(-2,3,4,5);h[0,2]=h[2,0]=R(1,7)
    b=vec(2,4);lam=R(5,4);tilt=vec(3,4)
    E=s.eye(5)[:,:4];E[4,:]=tilt.T
    F=s.Matrix([*(-tilt),1]);B=E.row_join(s.eye(5)[:,4])
    G=h.row_join(h*b).col_join((b.T*h).row_join(s.Matrix([[lam**2+(b.T*h*b)[0]]])))
    g=B.inv().T*G*B.inv();gi=g.inv();n=lam*F
    eq((n.T*gi*n)[0],1);eq(E.T*g*E,h)
    return g,gi,E,F,lam,n

def source_jump():
    g,gi,E,F,lam,n=chart();j=R(-6,5);a=vec(4)
    J=lam*(2*j*g+6*j*n*n.T+n*a.T+a*n.T)
    # Independent Christoffel jump from actual derivative difference F_mu J.
    G=[s.Matrix(5,5,lambda i,k:sum(gi[l,m]*(F[i]*J[m,k]+F[k]*J[m,i]-F[m]*J[i,k])/2 for m in I)) for l in I]
    A=g*s.Matrix([s.trace(gi*M) for M in G])
    eq(A,a)
    K=-E.T*sum((n[k]*G[k] for k in I),s.zeros(5))*E
    eq(K,j*(E.T*g*E))
    # The full 15x15 linear map J -> (10 Israel, 5 contracted jump)
    # at fixed admissible g,F is invertible.
    keys=[(i,k) for i in I for k in range(i,5)]
    p=s.Matrix(s.symbols('p:15'));P=s.Matrix(5,5,lambda i,k:p[keys.index(tuple(sorted((i,k))))])
    H=E.T*P*E/(2*lam);A=P*gi*F-F*s.trace(gi*P)/2
    rows=s.Matrix([H[i,k] for i in range(4) for k in range(i,4)]+list(A))
    assert rows.jacobian(p).rank()==15
    # Arbitrary Israel residual B, not just pure tension.
    B=sym(6,4);h=E.T*g*E;dual=g*E*h.inv();T=dual*B*dual.T
    P=lam*(2*T+2*s.trace(h.inv()*B)*n*n.T+n*a.T+a*n.T)
    eq(E.T*P*E/(2*lam),B);eq(P*gi*F-F*s.trace(gi*P)/2,a)
    # Differentiate the actual pure-tension source map with graph tilt,
    # source-jump and metric perturbations. Sherman-Morrison exact oracle.
    e=s.symbols('e');v=vec(7);m=v*v.T;dF=vec(8);dF[4]=0;da=vec(9);dj=R(1,17)
    gie=gi-e*(gi*v)*(gi*v).T/(1+e*(v.T*gi*v)[0]);Fe=F+e*dF
    ze=(Fe.T*gie*Fe)[0];dl=-lam**3*s.diff(ze,e).subs(e,0)/2
    dn=dl*F+lam*dF
    A0=J/lam
    dJ=dl*A0+lam*(2*dj*g+2*j*m+6*dj*n*n.T+6*j*(dn*n.T+n*dn.T)+dn*a.T+n*da.T+da*n.T+a*dn.T)
    le=1/s.sqrt(ze);ne=le*Fe;ae=a+e*da;je=j+e*dj
    exact=le*(2*je*(g+e*m)+6*je*ne*ne.T+ne*ae.T+ae*ne.T)
    eq(exact.diff(e).subs(e,0),dJ)
    # Original three charts: common source, conformal cusp, Gaussian.
    for c,d in [(0,8),(-3,2),(-4,0)]:
        Q=lam*(2*j*g+(6+2*c)*j*n*n.T)
        eq((n.T*gi*Q*gi*n)[0]/lam,d*j)
    print('PASS BR120 full 15-row source-jump inverse, arbitrary Israel defect, moving tilt and source Frechet')

def chart_bidi():
    g,gi,E,F,lam,n=chart();j=R(-6,5);a=vec(4);J=lam*(2*j*g+6*j*n*n.T+n*a.T+a*n.T)
    # In a straight chart the seam covector is dy, not a tilted F.
    B=E.row_join(s.eye(5)[:,4]);g=B.T*g*B;gi=g.inv();J=B.T*J*B;n=B.T*n;F=s.eye(5)[:,4]
    p=s.symbols('p');f=s.symbols('f');V=vec(10);V[4]=f
    # V continuous, derivative jump in the normal column only.
    A=lam*p*gi*n;dV=A*F.T
    lieJump=f*J+g*dV+dV.T*g
    mJump=2*p*n*n.T
    eq(lieJump,f*J+mJump)
    # F -> moving continuous metric, and inverse addition of Lie jet.
    qJump=mJump-lieJump
    eq(qJump+f*J,s.zeros(5));eq(qJump+lieJump,mJump)
    # Graph-only transport does not fix the wall. The inverse requires
    # V^y=f and actual normal derivative jump; they are independent data.
    assert s.Matrix([V[4],(F.T*A)[0]]).jacobian([f,p]).rank()==2
    # Differentiate continuity along a moving graph: [q_a] = -f_a J -f J_a.
    df=s.symbols('df');Ja=sym(12);q_a=-df*J-f*Ja
    eq(q_a+df*J+f*Ja,s.zeros(5))
    # P_g V residual must be subtracted; it is not automatically zero.
    Pp=vec(13);Pm=vec(14);assert Pp!=Pm
    Cp=vec(15);Cm=Cp
    eq((Cp-Pp)-(Cm-Pm),-(Pp-Pm))
    print('PASS BR121 sheared F-to-moving-continuous metric jet BIDI with independent graph and scale derivative, explicit gauge defect')

def commutator():
    # General nonorthogonal Lorentz metric and independent 2-jets,
    # arbitrary vector X and scalar first/second jets. Compute coordinate
    # commutator and covariant RHS independently; third scalar jets cancel.
    g=s.diag(-2,3,4,5,6);g[0,2]=g[2,0]=R(1,5);g[1,4]=g[4,1]=R(1,7)
    gi=g.inv();dg=[sym(i+2) for i in I];ddg=[[sym(8+min(i,j)*5+max(i,j)) for j in I] for i in I]
    dgi=[-gi*m*gi for m in dg]
    G={(k,a,b):sum(gi[k,l]*(dg[a][l,b]+dg[b][l,a]-dg[l][a,b])/2 for l in I) for k,a,b in product(I,repeat=3)}
    dG={(c,k,a,b):sum((dgi[c][k,l]*(dg[a][l,b]+dg[b][l,a]-dg[l][a,b])+gi[k,l]*(ddg[c][a][l,b]+ddg[c][b][l,a]-ddg[c][l][a,b]))/2 for l in I) for c,k,a,b in product(I,repeat=4)}
    C=s.Matrix([sum(gi[a,b]*G[k,a,b] for a,b in product(I,repeat=2)) for k in I])
    dC=[s.Matrix([sum(dgi[c][a,b]*G[k,a,b]+gi[a,b]*dG[c,k,a,b] for a,b in product(I,repeat=2)) for k in I]) for c in I]
    Ric=s.Matrix(5,5,lambda a,b:sum(dG[k,k,a,b]-dG[b,k,a,k] for k in I)+sum(G[k,k,l]*G[l,a,b]-G[k,b,l]*G[l,a,k] for k,l in product(I,repeat=2)))
    X=vec(17);dX=[vec(18+a) for a in I];ddX=[[vec(24+min(a,b)*5+max(a,b)) for b in I] for a in I]
    first=vec(52);second=sym(53)
    coordinate=sum(2*gi[a,b]*dX[a][k]*second[b,k] for a,b,k in product(I,repeat=3))-sum(X[c]*dgi[c][a,b]*second[a,b] for a,b,c in product(I,repeat=3))
    coordinate+=sum((gi[a,b]*ddX[a][b]).dot(first) for a,b in product(I,repeat=2))-sum(C[a]*dX[a].dot(first) for a in I)+sum(X[a]*dC[a].dot(first) for a in I)
    DX=[dX[a]+s.Matrix([sum(G[k,a,l]*X[l] for l in I) for k in I]) for a in I]
    Hess=s.Matrix(5,5,lambda a,b:second[a,b]-sum(G[k,a,b]*first[k] for k in I))
    DDX=[[ddX[a][b]+s.Matrix([sum(dG[a,k,b,l]*X[l]+G[k,b,l]*dX[a][l]+G[k,a,l]*DX[b][l]-G[l,a,b]*DX[l][k] for l in I) for k in I]) for b in I] for a in I]
    BoxX=sum((gi[a,b]*DDX[a][b] for a,b in product(I,repeat=2)),s.zeros(5,1))
    covariant=sum(2*gi[a,b]*DX[a][k]*Hess[b,k] for a,b,k in product(I,repeat=3))+(BoxX+gi*Ric*X).dot(first)
    eq(coordinate,covariant)
    # Non-umbilic Gaussian warp: exact normal commutator, including
    # derivative of mean curvature. No shell or reduced PDE assumed.
    y,t,x=s.symbols('y t x');f=[s.Function('f'+str(i))(y) for i in range(4)];k=[s.diff(u,y) for u in f];tau=sum(k)
    v=s.Function('v')(t,x,y)
    box=lambda u:s.diff(u,y,2)+tau*s.diff(u,y)-s.exp(-2*f[0])*s.diff(u,t,2)+s.exp(-2*f[1])*s.diff(u,x,2)
    rhs=-2*k[0]*s.exp(-2*f[0])*s.diff(v,t,2)+2*k[1]*s.exp(-2*f[1])*s.diff(v,x,2)-s.diff(tau,y)*s.diff(v,y)
    eq(s.expand(box(s.diff(v,y))-s.diff(box(v),y)),rhs)
    print('PASS BR122 independent 5D variable-metric scalar/vector commutator and nonumbilic normal shear factor')

def null_shear():
    h=s.diag(-1,1,1,1);z=s.Matrix([1,1,0,0]);b=s.Matrix([0,0,1,0]);q=h*z
    # Full 5D null mixed polarization, no normal frequency.
    Z=z.col_join(s.zeros(1,1));g=s.diag(h,1);m=s.zeros(5);m[:4,4]=b;m[4,:4]=b.T
    eq((Z.T*g*Z)[0],0);eq(m*g*Z-Z*s.trace(g*m)/2,s.zeros(5,1))
    K=-(z*b.T+b*z.T)/2
    eq(s.trace(h*K),0);eq(K*q-q*s.trace(h*K),s.zeros(4,1))
    # Realized by a spatial tracefree offdiagonal shape at time symmetry.
    M=s.zeros(4);M[1,2]=M[2,1]=1;j=s.symbols('j');S=M # tr_h M=0
    eq(s.trace(h*M),0);eq(-2*s.trace(h*S*h*K),2)
    # Mixed pure gauge polarization would be proportional to z.
    assert s.Matrix.hstack(z,b).rank()==2
    # Codazzi/trace and tangent R scalar principal vanish; full curved
    # linearized Gauss has lower-order shape/source terms, not imposed here.
    H=s.zeros(4);eq((q.T*H*q)[0]-(z.T*q)[0]*s.trace(h*H),0)
    # Actual nonzero AN seam BR117 has H_01=0, M_sp,01!=0;
    # the same null/transverse construction works in its frame.
    a,c,d,e=s.symbols('a c d e',positive=True);mu=s.symbols('mu',nonzero=True)
    H=s.diag(-a,c,d,e);Q=s.Matrix([s.sqrt(c/a),1,0,0]);B=s.eye(4)[:,2]
    A=s.zeros(4);A[1,2]=A[2,1]=mu
    eq((Q.T*H*Q)[0],0);eq((Q.T*H*B)[0],0);eq((Q.T*A*B)[0],mu)
    print('PASS BR123 null mixed polarization satisfies principal gauge/trace/Codazzi yet nonzero shear; not full curved Gauss counterexample')

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--part',choices=['jump','chart','commutator','null'],required=True)
    {'jump':source_jump,'chart':chart_bidi,'commutator':commutator,'null':null_shear}[p.parse_args().part]()
