#!/usr/bin/env python3
"""BR143-145: constraint trace algebra, G3 central tidal observable and signed quotient."""
import argparse
from itertools import combinations, combinations_with_replacement
import sympy as s
Q=s.Rational

def eq(a,b):
    if isinstance(a,s.MatrixBase): assert (a-b).applyfunc(s.simplify)==s.zeros(*a.shape)
    else: assert s.simplify(a-b)==0

def trace():
    I=range(5);P=list(combinations(I,2));pairs=list(combinations_with_replacement(range(10),2));eta=[-1,1,1,1,1]
    q=s.symbols('q:55');w=s.Matrix(10,10,lambda a,b:q[pairs.index(tuple(sorted((a,b))))])
    def W(a,b,c,d):
        if a==b or c==d:return s.S.Zero
        return (1 if a<b else -1)*(1 if c<d else -1)*w[P.index(tuple(sorted((a,b)))),P.index(tuple(sorted((c,d))))]
    rows=[W(a,b,c,d)+W(a,c,d,b)+W(a,d,b,c) for a,b,c,d in combinations(I,4)]
    rows += [sum(eta[a]*W(a,b,a,d) for a in I) for b,d in combinations_with_replacement(I,2)]
    V=s.Matrix.hstack(*s.Matrix(rows).jacobian(q).nullspace());X=s.Matrix(list(w)).jacobian(q)*V;G=X.T*X;P0=s.eye(100)-X*G.inv()*X.T
    M=[];D=[];trip=list(combinations(range(1,5),3))
    for i in range(1,5):
        A=s.zeros(10)
        for k in range(1,5):
            if i==k:continue
            a=P.index((0,k));b=P.index(tuple(sorted((i,k))));A[a,b]=A[b,a]=1 if i<k else -1
        M.append(s.kronecker_product(A,s.eye(10)))
        Z=s.zeros(50,100)
        for k in range(10):Z[k,10*P.index((0,i))+k]=1
        for j,(u,v,w) in enumerate(trip):
            if i not in (u,v,w):continue
            p,sg=((v,w),1) if i==u else ((u,w),-1) if i==v else ((u,v),1)
            for k in range(10):Z[10+10*j+k,10*P.index(p)+k]=sg
        D.append(Z)
    Dj=s.Matrix.hstack(*(d*X for d in D));Rj=s.Matrix.hstack(*(P0*a*X for a in M));ids=list(Dj.T.rref()[1]);Dr=Dj[ids,:]
    L=Dr.T.gauss_jordan_solve(Rj.T)[0].T;E0=Dj[:,Dj.rref()[1]];E=E0*E0[ids,:].inv()
    eq(L*Dr,Rj);eq(E*Dr,Dj)
    Sc=-L.T*M[3]*L-L.T*D[3].T*E-E.T*D[3]*L
    C=L[[10*P.index((i,j))+k for i,j in combinations(range(1,4),2) for k in range(10)],:]
    Ct=L[[10*P.index((i,j))+P.index((a,b)) for i,j in combinations(range(1,4),2) for a,b in combinations(range(1,4),2)],:]
    Z=s.Matrix.hstack(*Sc.nullspace());assert Sc.rank()==22
    print('BR143 ranks normal flux, full electric trace, spatial trace, kernel images:',Sc.rank(),C.rank(),Ct.rank(),(C*Z).rank(),(Ct*Z).rank())
    for T in (C,Ct):
        F=T*Z; J=s.Matrix.hstack(*(F[:,i] for i in F.rref()[1])) if F.rank() else s.zeros(T.rows,0)
        R=s.eye(T.rows)-J*(J.T*J).inv()*J.T if J.cols else s.eye(T.rows)
        U=Sc.T.gauss_jordan_solve((R*T).T)[0].T;eq(U*Sc,R*T);eq(R*T*Z,s.zeros(T.rows,Z.cols))
        assert J.cols+ (R*T).rank()==T.rank()
    assert (C*Z).rank()==4 and (Ct*Z).rank()==0 and Ct.rank()==3
    print('PASS BR143 normal-work kernel split, spatial Cartan trace factors through flux; full trace has four blind directions')

def tides():
    x,y,z,w=s.symbols('x y z w',real=True);v=(x,y,z,w);e,p=s.symbols('e p',real=True,nonzero=True);r2=x*x+y*y+z*z
    A=2*s.Matrix([2*x*z-2*y,2*x+2*y*z,1-x*x-y*y+z*z])/(1+r2)**2
    a=2*e*s.Matrix([-2*y+2*x*z,2*x+2*y*z,1-3*x*x-3*y*y-z*z]);psi=p*(1-Q(8,9)*e*e*r2)
    zero=dict.fromkeys(v,0)
    for i in range(3):
        eq((a-e*A).diff(v[i]).subs(zero),s.zeros(3,1))
        for j in range(3):eq((a-e*A).diff(v[i],v[j]).subs(zero),s.zeros(3,1))
    seed=(s.eye(3)+a*a.T).row_join(a).col_join(a.T.row_join(s.ones(1)))
    g=psi**2*seed;g0=g.subs(zero);gi=g0.inv();dg=[g.diff(t).subs(zero) for t in v];ddg=[[g.diff(t,u).subs(zero) for u in v] for t in v];dgi=[-gi*m*gi for m in dg];I=range(4)
    low=lambda d,a,b,k:(d[a][k,b]+d[b][k,a]-d[k][a,b])/2
    G={(k,a,b):sum(gi[k,m]*low(dg,a,b,m) for m in I) for k in I for a in I for b in I}
    dG=lambda t,k,a,b:sum(dgi[t][k,m]*low(dg,a,b,m)+gi[k,m]*low(ddg[t],a,b,m) for m in I)
    ric=s.Matrix(4,4,lambda a,b:sum(dG(k,k,a,b)-dG(b,k,a,k)+sum(G[k,k,m]*G[m,a,b]-G[k,b,m]*G[m,a,k] for m in I) for k in I)).applyfunc(s.simplify)
    H=s.eye(4);H[3,:3]=-a.subs(zero).T
    eq(H.T*g0*H,p*p*s.eye(4));T=(H.T*ric*H).applyfunc(s.simplify)
    target=s.diag(-Q(208,9)*e**2,-Q(208,9)*e**2,Q(80,9)*e**2,Q(112,3)*e**2);target[2,3]=target[3,2]=16*e
    eq(T,target);eq(s.trace(T),0)
    eq(target[2:4,2:4].det(),Q(8960,27)*e**4-256*e**2)
    assert target[2:4,2:4].det().subs(e,Q(1,4))<0
    print('PASS BR144 independent full spatial Ricci central jet, signed mixed tidal observable, zero trace')

def quotient():
    e,p=s.symbols('e p',real=True,nonzero=True);T=s.diag(-Q(208,9)*e**2,-Q(208,9)*e**2,Q(80,9)*e**2,Q(112,3)*e**2);T[2,3]=T[3,2]=16*e;T=T/p**2
    R=s.diag(1,1,1,-1);eq(T.subs(e,-e),R*T*R);eq(T[:3,:3],T.subs(e,-e)[:3,:3]);eq(T[3,3],T.subs(e,-e)[3,3]);eq(T[2,3]-T.subs(e,-e)[2,3],32*e/p**2)
    eq(p**2*T[2,3]/16,e)
    k=s.symbols('k');eq(T.charpoly(k).as_expr(),T.subs(e,-e).charpoly(k).as_expr())
    print('PASS BR145 oriented mixed tidal probe recovers sign; diagonal blocks and spectrum cannot')

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--part',choices=['trace','tides','quotient'],required=True)
    {'trace':trace,'tides':tides,'quotient':quotient}[p.parse_args().part]()
