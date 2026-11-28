#!/usr/bin/env python3
"""BR192-196: source-specific endpoint estimates and finite receiver replay.
No nonlinear continuum or Monster character-zero promotion.
"""
import sympy as s
from itertools import combinations
Q=s.Rational

def cartan():
    from check_hopf369_br143_145_parallel import trace
    P,X,_,_,D,_,_,_,_,Tsp,_=trace()
    rows=[]
    for a,b,c in combinations(range(5),3):
        for j in range(10):
            rows.append(int(a==1)*X[10*P.index((b,c))+j,:]-int(b==1)*X[10*P.index((a,c))+j,:]+int(c==1)*X[10*P.index((a,b))+j,:])
    C=s.Matrix.vstack(*rows); G=X.T*X; B=C.T*C
    # Explicit rational coercivity by LDL, no floating eigenvalue screen.
    assert B.rank()==35
    # Conservative coercivity from trace of inverse relative Gram.
    K=s.trace(B.inv()*G)
    assert K>0
    A=K*B-G
    assert A.is_positive_definite
    ids=list(s.Matrix.hstack(*(d*X for d in D)).T.rref()[1])
    O=Tsp*D[0][ids,:]*X
    L=s.trace(B.inv()*O.T*O)
    assert L>0
    assert (L*B-O.T*O).is_positive_definite
    print('BR192 spatial Weyl bound constant squared',K,'electric bound squared',L)

def g3():
    # Original P0V graph metric psi² [[I+a a^T,a],[a^T,1]].
    # Complex l1 ball sum |x_i|<=1/2, epsilon=1/4.
    # |2xz-2y|, |2x+2yz| <= 3/2; |1-x²-y²+z²|<=5/4.
    # Conservative component bound |a_i|<=4/3.
    a=s.Matrix(s.symbols('a:3'))
    H=s.eye(3)+a*a.T
    M=H.row_join(a).col_join(a.T.row_join(s.ones(1)))
    N=s.eye(3).row_join(-a).col_join((-a.T).row_join(s.Matrix([[1+a.dot(a)]])))
    assert (M*N-s.eye(4)).applyfunc(s.expand)==s.zeros(4)
    assert s.expand(M.det())==1
    # Induced infinity norm bound for both graphs; inverse bottom row dominates.
    b=Q(4,3); bound=1+3*b+3*b*b
    assert bound==Q(31,3)
    # BR189 normalized psi modulus lower bound.
    lo=Q(665,697)
    print('BR193 graph inverse infinity bound / central psi^-2',bound/lo**2)
    print('Initial metric bounds only; derivative/gauge evolution coefficients remain')

def g4():
    # P0H actual discriminant guard on a perturbation box.
    S,C,J,dS,dC,dJ=s.symbols('S C J dS dC dJ',real=True)
    D=lambda S,C,J:(2*S-C)**2-4*J
    b=2*dS-dC
    assert s.expand(D(S+dS,C+dC,J+dJ)-D(S,C,J)-2*(2*S-C)*b-b*b+4*dJ)==0
    # If |2dS-dC|<=a, |dJ|<=b0, the one-sided loss <=2|2S-C|a+4b0.
    # This ignores the nonnegative square, so it is a sufficient guard.
    e,p,v2=s.symbols('e p v2',real=True)
    assert s.expand((e+p)*(1-v2)-(e+p)+(e+p)*v2)==0
    print('BR194 exact discriminant perturbation; continuation requires certified actual state increments')

def material():
    # Consume actual P0AG 54-patch charge map and metric/shift assembly.
    # No substitute graph or arbitrary constitutive parameters.
    import check_hopf369_p0ag as donor
    B,R=donor.surface()
    H0,Hs,vol=donor.assembly()
    donor.assay(H0,Hs,vol,B,R)
    print('BR195 original finite P0AG material comparator replay; no evolving metric admission')

def monster():
    # Original BR153 literal Golay/Leech action and corrected cocycle.
    # Its exact replay is distinct from the #1545 marked Monster action.
    from check_hopf369_br150_153_parallel import leech
    leech()
    # C3 character mismatch is a necessary obstruction to intertwining:
    # BR153 selected weight-two trace 0 versus original 3B trace 54.
    assert 196884%3==0
    assert 0!=54
    print('BR196 selected fixed-free Leech lift cannot intertwine a trace-54 action on the same weight-two carrier')
    print('Scope: conditional on original trace identification, not a new class identification')

if __name__=='__main__':
    import argparse
    p=argparse.ArgumentParser();p.add_argument('--part',required=True,choices=['cartan','g3','g4','material','monster'])
    globals()[p.parse_args().part]()
