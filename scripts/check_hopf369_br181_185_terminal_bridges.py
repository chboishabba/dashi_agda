#!/usr/bin/env python3
"""BR181-185: terminal bridge checks; conditional algebra, not PDE acceptance."""
import sympy as s
from itertools import combinations
from check_hopf369_br143_145_parallel import trace

def cartan():
    P,X,_,_,D,L,E,Sc,T,Tsp,Z=trace()
    # Spatial axial covector, exact full exterior source reconstruction.
    rows=[]
    for a,b,c in combinations(range(5),3):
        for j in range(10):
            rows.append(int(a==1)*X[10*P.index((b,c))+j,:]-int(b==1)*X[10*P.index((a,c))+j,:]+int(c==1)*X[10*P.index((a,b))+j,:])
    C=s.Matrix.vstack(*rows)
    assert C.rank()==35
    U=(C.T*C).inv()*C.T
    assert U*C==s.eye(35)
    # Source-compatible inverse and orthogonal residual; no arbitrary source promotion.
    assert (C*U).T==C*U
    assert C.T*(s.eye(C.rows)-C*U)==s.zeros(35,C.rows)
    ids=list(s.Matrix.hstack(*(d*X for d in D)).T.rref()[1])
    O=Tsp*D[0][ids,:]*X
    assert O*U*C==O
    print('PASS BR181 axial inhomogeneous Cartan inverse and electric source factorization')

def radial():
    l,m,e,I0,I1,I2=s.symbols('l m e I0 I1 I2', positive=True)
    a=e*l**5*I1/(12*m);c=e*l**5*I0/(12*m)
    dl=lambda f:s.diff(f,l)-I1*s.diff(f,I0)-I2*s.diff(f,I1)
    J=s.Matrix([[dl(a),s.diff(a,e)],[dl(c),s.diff(c,e)]])
    assert s.simplify(J.det()+e*l**10*(I0*I2-I1**2)/(144*m*m))==0
    # Degenerate norm observation has explicit tangent to level set.
    g=a*a+c*c
    n=s.Matrix([s.diff(g,e),-dl(g)])
    assert s.simplify((s.Matrix([[dl(g),s.diff(g,e)]])*n)[0])==0
    # Signed marked observation retains amplitude derivative at zero.
    assert J.subs(e,0)[:,0]==s.zeros(2,1)
    assert J.subs(e,0)[:,1]!=s.zeros(2,1)
    print('PASS BR182 radial degenerate tangent and signed zero-fibre differential')

def shell():
    # Exact functorial one-body lift on the original eight spin-orbital labels.
    # Applies to BR172 H and #886 interactions, does not construct Coulomb integrals.
    n=8; pairs=list(combinations(range(n),2))
    def lift(H):
        return s.Matrix(len(pairs),len(pairs),lambda p,q:
            H[pairs[p][0],pairs[q][0]]*int(pairs[p][1]==pairs[q][1])
            -H[pairs[p][0],pairs[q][1]]*int(pairs[p][1]==pairs[q][0])
            -H[pairs[p][1],pairs[q][0]]*int(pairs[p][0]==pairs[q][1])
            +H[pairs[p][1],pairs[q][1]]*int(pairs[p][0]==pairs[q][0]))
    H=s.Matrix(n,n,lambda i,j:s.Rational((i+1)*(j+1),17+i+j))
    K=s.diag(*range(n))
    assert lift(H).T==lift(H)
    assert lift(H*K-K*H)==lift(H)*lift(K)-lift(K)*lift(H)
    assert lift(s.eye(n))==2*s.eye(len(pairs))
    print('PASS BR183 wedge2 operator lift and commutator (28 states, selected test)')

def observables():
    # BR144/145 actual central tidal tensor; same marked residual.
    e,p=s.symbols('e p',real=True,nonzero=True)
    T=s.diag(-s.Rational(208,9)*e**2,-s.Rational(208,9)*e**2,s.Rational(80,9)*e**2,s.Rational(112,3)*e**2)
    T[2,3]=T[3,2]=16*e
    T=T/p**2
    M=s.diag(1,1,1,-1)
    assert T.subs(e,-e)==M*T*M
    assert s.simplify(p**2*T[2,3]/16-e)==0
    # Exact two-way decomposition; even data alone lose marked sign.
    assert (T+M*T*M)/2+(T-M*T*M)/2==T
    print('PASS BR184 G3 marked tidal residual reconstruction (initial jet only)')

def material():
    # Discrete same-current transfer: exact incidence and boundary work.
    # Generic interface test, not original PNP/RMHD source admission.
    B=s.Matrix([[-1,0,0],[1,-1,0],[0,1,-1],[0,0,1]])
    j=s.Matrix(s.symbols('j:3'));v=s.Matrix(s.symbols('v:4'))
    assert (s.ones(1,4)*B)==s.zeros(1,3)
    assert (v.T*B*j)[0]==( (B.T*v).T*j)[0]
    print('PASS BR185 reciprocal incidence work interface (generic, no receiver claim)')

if __name__=='__main__':
    import argparse
    p=argparse.ArgumentParser();p.add_argument('--part',required=True,choices=['cartan','radial','shell','observables','material'])
    globals()[p.parse_args().part]()
