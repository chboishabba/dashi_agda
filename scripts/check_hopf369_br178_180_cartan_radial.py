#!/usr/bin/env python3
"""BR178-180: frozen same-source symbol, observable Gram, radial Jacobian.
Run locally; not curved constraint propagation or physical calibration.
"""
import sympy as s
from check_hopf369_br143_145_parallel import trace
from check_hopf369_br_curvature_energy import carrier

def symbol():
    P,X,_,_,D,L,E,Sc,T,Tsp,Z=trace()
    _,_,X0,G,_,_,_,A,_,R,_,_=carrier()
    assert X==X0
    ids=list(s.Matrix.hstack(*(d*X for d in D)).T.rref()[1])
    for k,l in [(1,0),(1,1),(2,1),(3,2),(0,1)]:
        Axi=k*A[0]+l*A[3]
        Dxi=(k*D[0]+l*D[3])[ids,:]*X
        # For stationary spatial covectors, full closure on first
        # curvature pair requires spatial exterior closure AND
        # time-space exterior closure (not just D divergence).
        xi=[0,k,0,0,l]
        from itertools import combinations
        rows=[]
        for a,b,c in combinations(range(5),3):
            for j in range(10):
                rows.append(xi[a]*X[10*P.index((b,c))+j,:]-xi[b]*X[10*P.index((a,c))+j,:]+xi[c]*X[10*P.index((a,b))+j,:])
        C=s.Matrix.vstack(*rows)
        V=s.Matrix.hstack(*Axi.nullspace())
        O=Tsp*Dxi*V
        Q=O.T*O
        assert Q.rank()==O.rank()
        # Ricci-free algebraic Weyl plus full closed curvature at
        # a non-null stationary covector implies zero curvature.
        assert C.rank()==35
        assert (C*V).rank()==V.cols
        print('BR178/179',k,l,'stationary dimension',V.cols,'observable rank',O.rank(),'closed stationary dimension',0)
    print('PASS sampled stationary full exterior closure and observable Gram')

def radial():
    lam,m,e,I0,I1,I2=s.symbols('lam m e I0 I1 I2', positive=True)
    a=e*lam**5*I1/(12*m); c=e*lam**5*I0/(12*m)
    dl=lambda f:s.diff(f,lam)-I1*s.diff(f,I0)-I2*s.diff(f,I1)
    J=s.Matrix([[dl(a),s.diff(a,e)],[dl(c),s.diff(c,e)]])
    assert s.simplify(J.det()+e*lam**10*(I0*I2-I1**2)/(144*m**2))==0
    J2=s.diag(2*a,2*c)*J
    assert s.simplify(J2.det()-4*a*c*J.det())==0
    assert J2.subs(e,0)==s.zeros(2)
    print('PASS BR180 signed and squared radial Jacobian, zero amplitude')
if __name__=='__main__':
    import argparse
    p=argparse.ArgumentParser();p.add_argument('--part',choices=['symbol','radial'],required=True)
    {'symbol':symbol,'radial':radial}[p.parse_args().part]()
