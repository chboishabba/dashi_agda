#!/usr/bin/env python3
"""Actual moving-normal Israel jump and reflection derivatives at the reference wall."""
import sympy as s
from itertools import combinations

def run(X,G,Y,J,F):
    P=list(combinations(range(5),2)); eta=s.diag(-1,1,1,1,1); n=s.eye(5)[:,4]
    left=G.inv()*X.T; I=s.eye(35)
    def wedge(a,b):
        return s.Matrix(10,10,lambda i,j:a[P[i][0],P[j][0]]*b[P[i][1],P[j][1]]+b[P[i][0],P[j][0]]*a[P[i][1],P[j][1]]-a[P[i][0],P[j][1]]*b[P[i][1],P[j][0]]-b[P[i][0],P[j][1]]*a[P[i][1],P[j][0]])
    def ext(A):
        return s.Matrix(10,10,lambda i,j:A[P[i][0],P[j][0]]*A[P[i][1],P[j][1]]-A[P[i][0],P[j][1]]*A[P[i][1],P[j][0]])
    def d_ext(A,H):
        return ext(A+H)-ext(A)-ext(H)
    N=n*n.T; R=s.eye(5)-2*N*eta; L=ext(R)
    assert s.kronecker_product(L,L)*X==X*F
    for i in range(4):
        K=s.zeros(5); K[i,4]=1; K[4,i]=1 if i==0 else -1
        assert K*eta+eta*K.T==s.zeros(5)
        dn=K*n; dN=dn*n.T+n*dn.T
        assert (n.T*eta*dn)[0]==0
        A=d_ext(s.eye(5),K); T=s.kronecker_product(A,s.eye(10))+s.kronecker_product(s.eye(10),A)
        O=left*T*X; assert X*O==T*X
        dL=d_ext(R,-2*dN*eta)
        dF=left*(s.kronecker_product(dL,L)+s.kronecker_product(L,dL))*X
        assert dF==O*F-F*O and dF*F+F*dF==s.zeros(35)
        for j in range(9):
            M=s.zeros(5); M[:4,:4]=s.Matrix(4,4,list(Y[:,j])); dM=K*M+M*K.T
            assert dM*eta*n+M*eta*dn==s.zeros(5,1)
            V=-wedge(eta,M)+3*wedge(N,M)
            dV=-wedge(eta,dM)+3*wedge(dN,M)+3*wedge(N,dM)
            assert s.Matrix(list(V))==X*J[:,j]
            assert s.Matrix(list(dV))==X*O*J[:,j]
        assert dF*J+F*O*J==O*J
        print('normal generator',i,'reflection and 9 jump columns PASS',flush=True)
    print('PASS BR207 moving normal exact derivatives',s.__version__,flush=True)

if __name__=='__main__':
    from check_hopf369_br_curvature_energy import carrier,P,Q
    _,V,X,G,Y,_,J,_,_,_,_,_=carrier()
    F=V.gauss_jordan_solve(s.diag(*[(-1)**(int(4 in P[a])+int(4 in P[b])) for a,b in Q])*V)[0]
    run(X,G,Y,J,F)
