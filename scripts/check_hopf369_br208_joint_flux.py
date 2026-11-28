#!/usr/bin/env python3
"""Joint observer/normal Bel flux derivative on original Weyl carrier."""
import sympy as s
from itertools import combinations,product

def run(X,bel):
    P=list(combinations(range(5),2)); I=range(5); eta=s.diag(-1,1,1,1,1)
    for seed in (1,2):
        m=s.Matrix(10,10,list(X*s.Matrix([s.Rational((seed*(k+2)**2+3*k)%17-8,7) for k in range(35)])))
        for i,j in combinations(I,2):
            K=s.zeros(5); K[j,i]=1; K[i,j]=1 if i==0 else -1
            assert K*eta+eta*K.T==s.zeros(5)
            L=s.Matrix(10,10,lambda a,b:K[P[a][0],P[b][0]]*int(P[a][1]==P[b][1])-K[P[a][0],P[b][1]]*int(P[a][1]==P[b][0])-K[P[a][1],P[b][0]]*int(P[a][0]==P[b][1])+K[P[a][1],P[b][1]]*int(P[a][0]==P[b][0]))
            dm=L*m+m*L.T
            a,b,c,d=4,0,0,0
            # Polarization of quadratic Bel tensor gives exact curvature derivative.
            dw=(bel(m+dm,a,b,c,d)-bel(m-dm,a,b,c,d))/2
            # Contravectors transform contragrediently to covariant components.
            H=-K.T
            dn=sum(H[k,a]*bel(m,k,b,c,d) for k in I if H[k,a])
            dt=sum(H[k,b]*bel(m,a,k,c,d)+H[k,c]*bel(m,a,b,k,d)+H[k,d]*bel(m,a,b,c,k) for k in I if H[k,0])
            assert dw+dn+dt==0,(seed,i,j,dw,dn,dt)
            if i==0 and j==4 and seed==1: assert dn!=0 and dt!=0
            print('seed',seed,'generator',i,j,'joint flux PASS',flush=True)
    print('PASS BR208 simultaneous curvature/observer/normal flux derivative',s.__version__)

if __name__=='__main__':
    from check_hopf369_br_curvature_energy import carrier,bel
    _,_,X,*_=carrier()
    run(X,bel)
