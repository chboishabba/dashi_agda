#!/usr/bin/env python3
"""Exact Bianchi-to-Bel current source factor on original Weyl jet carrier."""
import sympy as s
from itertools import combinations

def run(X,G,A,bel):
    I=range(5); P=list(combinations(I,2)); triples=list(combinations(I,3)); eta=[-1,1,1,1,1]
    def signed(seq,keys):
        if len(set(seq))!=len(seq): return None,0
        return keys.index(tuple(sorted(seq))),(-1)**sum(a>b for i,a in enumerate(seq) for b in seq[i+1:])
    # C_{abc,de}=∂a W_{bc,de}-∂b W_{ac,de}+∂c W_{ab,de}.
    C=s.zeros(100,175)
    for t,(a,b,c) in enumerate(triples):
        for j in range(10):
            for axis,pair,sg in ((a,(b,c),1),(b,(a,c),-1),(c,(a,b),1)):
                C[10*t+j,35*axis:35*(axis+1)]+=sg*X[10*P.index(pair)+j,:]
    # Div W_{b,de}=sum_a eta_a C_{ade,ab}, by pair symmetry and Ricci-free jets.
    B=s.zeros(100)
    for i,(a,b) in enumerate(P):
        for j,(d,e) in enumerate(P):
            row=10*i+j
            if a==0:
                for k in I:
                    t,sg=signed((k,d,e),triples); p,sg2=signed((k,b),P)
                    if sg and sg2:B[row,10*t+p]-=eta[k]*sg*sg2
            else:
                B[row,10*triples.index((0,a,b))+j]=1
    R=s.Matrix.hstack(s.eye(35),*(-a for a in A))
    assert X.T*B*C==G*R
    for seed in (1,2):
        w=s.Matrix([s.Rational((seed*(k+2)**2+3*k)%17-8,7) for k in range(35)])
        m=s.Matrix(10,10,list(X*w))
        jets=[s.Matrix([s.Rational(((i+2)*(k+3)+seed*k*k)%19-9,11) for k in range(35)]) for i in I]
        z=s.Matrix.vstack(*jets)
        div=0
        for i in I:
            dm=s.Matrix(10,10,list(X*jets[i])); div+=eta[i]*(bel(m+dm,i,0,0,0)-bel(m-dm,i,0,0,0))/2
        assert div==-(w.T*G*R*z)[0]==-(w.T*X.T*B*C*z)[0]
        assert div!=0
        print('seed',seed,'Bel divergence = Bianchi source',div,flush=True)
    print('PASS BR209 exact 35x175 source factor and two Bel divergence states',s.__version__,flush=True)

if __name__=='__main__':
    from check_hopf369_br_curvature_energy import carrier,bel
    _,_,X,G,_,_,_,A,_,_,_,_=carrier()
    run(X,G,A,bel)
