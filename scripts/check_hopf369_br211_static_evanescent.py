#!/usr/bin/env python3
"""BR211: full physical exterior-closed static evanescent Israel jump.
Original BR27 and BR175 carriers, not full glancing estimate."""
import sympy as s
from itertools import combinations

def run(X,G,Y,H,J,A,B,R,F):
    P=list(combinations(range(5),2)); I=s.eye(35)
    def exterior(xi):
        return s.Matrix.vstack(*(xi[a]*X[10*P.index((b,c))+j,:]-xi[b]*X[10*P.index((a,c))+j,:]+xi[c]*X[10*P.index((a,b))+j,:] for a,b,c in combinations(range(5),3) for j in range(10)))
    C=exterior([0,s.I,0,0,-1]); N=s.Matrix.hstack(*C.nullspace()); print('complex null kernel',N.cols,flush=True); assert N.cols==5
    assert (s.I*A[0]-A[3])*N==s.zeros(35,5)
    assert exterior([0,s.I,0,0,1])*F*N==s.zeros(100,5)
    j=s.Rational(-6,5)
    E=(I-F)*N; D=(I+F)*N
    assert D.rank()==E.rank()==5
    print('even odd ranks',D.rank(),E.rank(),flush=True)
    k=s.symbols('k',positive=True)
    top=E.row_join(D).row_join(-j*J)
    bot=s.zeros(9,5).row_join(-R*N).row_join(s.I*k*B[0])
    T=top.col_join(bot)
    assert top.rank()==19
    print('jump only rank',top.rank(),'joint ranks',[(v,T.subs(k,v).rank()) for v in (1,2,10)],flush=True)
    ns=top.nullspace()
    ids=list(top.T.rref()[1]); minor=top[ids,:]; det=s.expand(minor.det()); print("minor rows",ids,"det",det,flush=True); assert len(ids)==19 and det!=0
    print("Gram determinant",s.factor((top.H*top).det()),flush=True)
    assert not ns
    print('jump kernel',len(ns),flush=True)
    print('PASS static complex null audit',flush=True)

if __name__=='__main__':
    from check_hopf369_br_curvature_energy import carrier,P,Q
    _,V,X,G,Y,H,J,A,B,R,_,_=carrier()
    F=V.gauss_jordan_solve(s.diag(*[(-1)**(int(4 in P[a])+int(4 in P[b])) for a,b in Q])*V)[0]
    run(X,G,Y,H,J,A,B,R,F)
