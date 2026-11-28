#!/usr/bin/env python3
"""BR40a actual warped Gaussian scalar/covector/tensor cutoff identity.
Split --sector/--index to enable 90s checkpointed local execution.
No full variable-coefficient PDE existence or uniform estimate claim.
"""
import argparse
import sympy as S

def run(sector,index):
    T,X,Y,Z,N=S.symbols('t x y z n')
    coords=(T,X,Y,Z,N);b=1+N;k=1/b
    signs=(-1,1,1,1)
    metric=S.diag(-b*b,b*b,b*b,b*b,1)
    inv=S.diag(-1/b**2,1/b**2,1/b**2,1/b**2,1)
    G={(4,a,c): -b*k*b*signs[a]*(a==c) for a in range(4) for c in range(4)}
    for a in range(4):
        G[a,4,a]=k;G[a,a,4]=k
    gamma=lambda l,i,j:G.get((l,i,j),S.Integer(0))
    # Independent coordinate Christoffel derivation; no substitution of
    # previously implemented connection into the oracle.
    for l in range(5):
        for i in range(5):
            for j in range(5):
                direct=S.expand(sum(inv[l,m]*(S.diff(metric[m,j],coords[i])
                    +S.diff(metric[m,i],coords[j])-S.diff(metric[i,j],coords[m]))/2
                    for m in range(5)))
                assert S.cancel(direct-gamma(l,i,j))==0,(l,i,j)
    chi=1+N*N*(T+X)+T*Y
    def hess(i,j):
        return S.diff(chi,coords[i],coords[j])-sum(gamma(l,i,j)*S.diff(chi,coords[l]) for l in range(5))
    if sector=='scalar':
        u=1+T*X+N*Y+Z*Z
        d=lambda i:S.diff(u,coords[i])
        covsecond=lambda i,j:S.diff(u,coords[i],coords[j])-sum(gamma(l,i,j)*d(l) for l in range(5))
        C=lambda f:sum(inv[i,i]*(S.diff(f,coords[i],2)-sum(gamma(l,i,i)*S.diff(f,coords[l]) for l in range(5))) for i in range(5))
        defect=sum(inv[i,i]*(hess(i,i)*u+2*S.diff(chi,coords[i])*d(i)) for i in range(5))
        assert S.cancel(C(chi*u)-chi*C(u)-defect)==0
    elif sector in ('covector','tensor'):
        rank=1 if sector=='covector' else 2
        size=5 if rank==1 else 25
        carrier=[1+(m+1)*T+(m+2)*X*N+(m%3)*Y*Z for m in range(size)]
        if rank==2:
            carrier=[(carrier[5*i+j]+carrier[5*j+i])/2 for i in range(5) for j in range(5)]
        U=lambda a:carrier[a[0]] if rank==1 else carrier[5*a[0]+a[1]]
        from itertools import product
        axes=list(product(range(5),repeat=rank))
        def first(u,i,a):
            ans=S.diff(u(a),coords[i])
            for place in range(rank):
                ans-=sum(gamma(l,i,a[place])*u(a[:place]+(l,)+a[place+1:]) for l in range(5))
            return ans
        def lap(u,a):
            ans=0
            for i in range(5):
                v=lambda idx:first(u,i,idx)
                second=S.diff(v(a),coords[i])-sum(gamma(l,i,i)*first(u,l,a) for l in range(5))
                for place in range(rank):
                    second-=sum(gamma(l,i,a[place])*v(a[:place]+(l,)+a[place+1:]) for l in range(5))
                ans+=inv[i,i]*second
            return ans
        a=axes[index]
        shifted=lambda idx:chi*U(idx)
        defect=sum(inv[i,i]*(hess(i,i)*U(a)+2*S.diff(chi,coords[i])*first(U,i,a)) for i in range(5))
        assert S.cancel(lap(shifted,a)-chi*lap(U,a)-defect)==0,(sector,a)
    else:raise ValueError(sector)
    print('PASS',sector,index,'125 Christoffels + full warped covariant cutoff identity')

if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('--sector',choices=['scalar','covector','tensor'],default='scalar')
    p.add_argument('--index',type=int,default=0)
    a=p.parse_args()
    assert 0<=a.index<({'scalar':1,'covector':5,'tensor':25}[a.sector])
    run(a.sector,a.index)
