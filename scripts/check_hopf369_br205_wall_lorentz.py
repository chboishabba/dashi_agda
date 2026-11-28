#!/usr/bin/env python3
"""BR205: actual wall-tangent Lorentz action on original Weyl/Israel carriers.
BR206: scalar transfer and Young identities only, not a trace estimate."""
import sympy as s
from itertools import combinations, combinations_with_replacement

def run(X,G,Y,H,J,F):
    P=list(combinations(range(5),2)); left=G.inv()*X.T
    for i,j in combinations(range(4),2):
        K=s.zeros(5);K[j,i]=1;K[i,j]=1 if i==0 else -1
        L=s.Matrix(10,10,lambda a,b:K[P[a][0],P[b][0]]*int(P[a][1]==P[b][1])-K[P[a][0],P[b][1]]*int(P[a][1]==P[b][0])-K[P[a][1],P[b][0]]*int(P[a][0]==P[b][1])+K[P[a][1],P[b][1]]*int(P[a][0]==P[b][0]))
        T=s.kronecker_product(L,s.eye(10))+s.kronecker_product(s.eye(10),L)
        O=left*T*X
        k=K[:4,:4]; U=s.kronecker_product(k,s.eye(4))+s.kronecker_product(s.eye(4),k)
        B=H.inv()*Y.T*U*Y
        assert X*O==T*X and Y*B==U*Y
        assert O*J==J*B and O*F==F*O
        sign=1 if i==0 else -1
        assert O.T*G==sign*G*O and B.T*H==sign*H*B
        if i==0: assert B*(B**2-s.eye(9))*(B**2-4*s.eye(9))==s.zeros(9)
        print(i,j,'PASS',flush=True)
    print('PASS wall Lorentz generator intertwiners',s.__version__)

def scalar():
    u,v,c=s.symbols('u v c',real=True)
    assert s.expand(u*(c*v)+v*(-c*u))==0
    x,y,d=s.symbols('x y d',positive=True)
    assert s.factor(d*x*x+y*y/d-2*x*y)==(d*x-y)**2/d
    print('PASS BR206 transfer cancellation and trace Young identity',s.__version__)

if __name__=='__main__':
    from check_hopf369_br_curvature_energy import carrier,P,Q
    _,V,X,G,Y,H,J,_,_,_,_,_=carrier()
    F=V.gauss_jordan_solve(s.diag(*[(-1)**(int(4 in P[a])+int(4 in P[b])) for a,b in Q])*V)[0]
    run(X,G,Y,H,J,F)
    scalar()
