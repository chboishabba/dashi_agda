#!/usr/bin/env python3
"""Original physical Weyl/Israel jump on a regular complex-null chart."""
import sympy as s
from itertools import combinations

def run(X,G,J,F,B,Rwall):
    P=list(combinations(range(5),2)); left=G.inv()*X.T
    t,l=s.symbols('t l'); xi=s.Matrix([t,s.I,0,0,-l])
    vs=[s.Matrix([l,0,0,0,-t]),s.eye(5)[:,2],s.eye(5)[:,3]]
    U=s.Matrix.hstack(*(s.Matrix([xi[a]*v[b]-xi[b]*v[a] for a,b in P]) for v in vs))
    pol=[s.diag(1,1,0),s.diag(1,0,1)]+[s.eye(3)[:,i]*s.eye(3)[:,j].T+s.eye(3)[:,j]*s.eye(3)[:,i].T for i,j in combinations(range(3),2)]
    Z=s.Matrix.hstack(*(s.Matrix(list(U*p*U.T)) for p in pol))
    N=(left*Z).applyfunc(s.expand)
    reduce=lambda m:m.applyfunc(lambda x:s.rem(s.expand(x),l*l-t*t-1,l))
    assert reduce(X*N-Z)==s.zeros(100,5)
    C=s.Matrix.vstack(*(xi[a]*Z[10*P.index((b,c))+j,:]-xi[b]*Z[10*P.index((a,c))+j,:]+xi[c]*Z[10*P.index((a,b))+j,:] for a,b,c in combinations(range(5),3) for j in range(10)))
    assert C==s.zeros(100,5)
    I=s.eye(35)
    T=((I-F)*N).row_join((I+F)*N).row_join(s.Rational(6,5)*J)
    for v,w,rank in [(0,1,19),(s.Rational(3,4),s.Rational(5,4),19),(3*s.I/5,s.Rational(4,5),19),(s.I,0,13),(-s.I,0,13)]:
        n=N.subs({t:v,l:w}); a=T.subs({t:v,l:w})
        assert n.rank()==5 and a.rank()==rank
        ns=a.nullspace(); shape=s.Matrix.hstack(*ns)[10:,:].rank() if ns else 0
        assert shape==(1 if rank==13 else 0)
        print(v,w,n.rank(),a.rank(),'jump nullity',len(ns),'shape rank',shape,flush=True)
    u=s.symbols('u',real=True)
    R=T.subs({t:s.I*(1-u*u)/(1+u*u),l:2*u/(1+u*u)}).applyfunc(s.cancel)
    ids=list(R.subs(u,1).T.rref()[1]); det=s.factor(R[ids,:].det(method='domain-ge'))
    assert s.cancel(det-10567230160896*s.I*u**7*(u**4+1)**2/(1953125*(u*u+1)**11))==0
    print('minor rows',ids,'det',det,flush=True)
    for sig in (-1,1):
        n=N.subs({t:sig*s.I,l:0}); top=T.subs({t:sig*s.I,l:0})
        for k in (1,2,10):
            bot=s.zeros(9,5).row_join(Rwall*n).row_join(k*s.I*(sig*s.eye(9)-B))
            joint=top.col_join(bot); ns=joint.nullspace()
            assert joint.rank()==15 and len(ns)==4
            assert s.Matrix.hstack(*ns)[10:,:].rank()==1
            print('glancing joint',sig,k,15,4,1,flush=True)
    print('PASS BR212 regular null chart, exact minor and glancing rank loss')

if __name__=='__main__':
    from check_hopf369_br_curvature_energy import carrier,P,Q
    _,V,X,G,Y,H,J,A,B,R,_,_=carrier()
    F=V.gauss_jordan_solve(s.diag(*[(-1)**(int(4 in P[a])+int(4 in P[b])) for a,b in Q])*V)[0]
    run(X,G,J,F,B[0],R)
