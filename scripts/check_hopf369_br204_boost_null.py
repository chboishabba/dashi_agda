#!/usr/bin/env python3
"""BR204: observer boost on signed null branches; no curved PDE claim."""
import sympy as s
from itertools import combinations
Q=s.Rational

def run(X,G,A):
    pairs=list(combinations(range(5),2)); I=s.eye(35); left=G.inv()*X.T
    def gen(K):
        L=s.Matrix(10,10,lambda i,j: K[pairs[i][0],pairs[j][0]]*int(pairs[i][1]==pairs[j][1])-K[pairs[i][0],pairs[j][1]]*int(pairs[i][1]==pairs[j][0])-K[pairs[i][1],pairs[j][0]]*int(pairs[i][0]==pairs[j][1])+K[pairs[i][1],pairs[j][1]]*int(pairs[i][0]==pairs[j][0]))
        T=s.kronecker_product(L,s.eye(10))+s.kronecker_product(s.eye(10),L)
        O=left*T*X
        assert X*O==T*X
        return O
    def proj(B):return (4*B**4-B**2)/3
    def dp(B,H):return (4*sum((B**j*H*B**(3-j) for j in range(4)),s.zeros(35))-B*H-H*B)/3
    for i in range(1,5):
        K=s.zeros(5);K[0,i]=K[i,0]=1
        O=gen(K)
        assert O.T*G==G*O
        assert O*(O*O-I)*(O*O-4*I)==s.zeros(35)
        for j in range(1,5):
            B=A[j-1]; P=proj(B)
            for sign in (-1,1):
                F=(I+sign*B)*P/2
                H=sign*(A[i-1]-int(i==j)*B)
                dF=((I+sign*B)*dp(B,H)+sign*H*P)/2
                assert F.rank()==5 and F*F==F
                assert (I-F)*O*F==dF*F
                assert F*dF+dF*F==dF
                assert F*dF*F==s.zeros(35)
        print('boost',i,'eight signed axial branches PASS',flush=True)
    print('PASS BR204 signed null boost tangency, positive Gram boost spectrum',s.__version__,flush=True)

if __name__=='__main__':
    from check_hopf369_br_curvature_energy import carrier
    _,_,X,G,_,_,_,A,_,_,_,_=carrier()
    run(X,G,A)
