#!/usr/bin/env python3
"""Exact diagonal of classical prime modular correspondence, p=41.
Only external analytic input: standard modularity and q expansion of j.
No class number or CM integrality theorem used.
"""
from time import perf_counter
from math import gcd
from sympy import Poly, symbols, ZZ

def convolution(a,b,n):
    out=[0]*(n+1)
    for i,x in enumerate(a[:n+1]):
        if x:
            for j,y in enumerate(b[:n+1-i]):
                out[i+j]+=x*y
    return out

def j_unit(n):
    # J=q*j = E4^3 / prod(1-q^m)^24.
    s1=[0]*(n+1);s3=[0]*(n+1)
    for d in range(1,n+1):
        for k in range(d,n+1,d):
            s1[k]+=d;s3[k]+=d**3
    e=[1]+[240*x for x in s3[1:]]
    # inverse eta product logarithmic derivative 24 sigma1.
    inv=[1]
    for k in range(1,n+1):
        v=sum(24*s1[i]*inv[k-i] for i in range(1,k+1))
        a,b=divmod(v,k);assert b==0;inv.append(a)
    return convolution(convolution(convolution(e,e,n),e,n),inv,n)

def diagonal(p, logder_fn=None):
    n=2*p; M=p*n
    # H(t)=J(t^p)-t^(p-1)J(t) = t^p (j(t^p)-j(t)).
    J=j_unit(M-p+1)
    H=[0]*(M+1)
    for i in range(n+1):H[p*i]+=J[i]
    for i in range(M-p+2):H[i+p-1]-=J[i]
    assert H[0]==1
    # L=t H'/H, computed exactly; use sparse leading support.
    if logder_fn is None:
        support=[(i,h) for i,h in enumerate(H) if i and h]
        L=[0]*(M+1)
        for k in range(1,M+1):
            v=k*H[k]
            for i,h in support:
                if i>=k:break
                v-=h*L[k-i]
            L[k]=v
    else:
        L=logder_fn(H)
    N=[1]
    for k in range(1,n+1):
        v=sum(L[p*i]*N[k-i] for i in range(1,k+1))
        a,b=divmod(v,k);assert b==0;N.append(a)
    # q^2p Phi_p(j(q),j(q)) = (q^(p-1) J(q)-J(q^p))*N(q).
    g=[0]*(n+1)
    for i in range(n-p+2):g[i+p-1]+=J[i]
    for i in range(3):g[i*p]-=J[i]
    rem=convolution(g,N,n)
    powers=[[1]+[0]*n]
    for k in range(n):powers.append(convolution(powers[-1],J[:n+1],n))
    coeff=[0]*(n+1)
    for d in range(n,-1,-1):
        c=rem[n-d];coeff[d]=c
        for k in range(d+1):rem[n-d+k]-=c*powers[d][k]
    assert not any(rem) and coeff[-1]==-1
    return Poly.from_list(coeff[::-1],symbols('X'),domain=ZZ)

def main():
    start=perf_counter(); X=symbols('X')
    p=41
    # tau^2+tau+41=0; multiplication by tau on basis (1,tau).
    from sympy import Matrix
    A=Matrix([[0,-41],[1,-1]])
    assert A.det()==41 and A*A+A+41*Matrix.eye(2)==Matrix.zeros(2)
    assert gcd(*[int(x) for x in A])==1
    P=diagonal(p)
    print('diagonal degree',P.degree(),'elapsed',perf_counter()-start,flush=True)
    K=-640320**3
    factor=Poly(X-K,X,domain=ZZ); multiplicity=0; S=P
    while S.eval(K)==0:
        S=S.exquo(factor);multiplicity+=1
    assert multiplicity>0
    # On |X-K|<=1/2, constant term dominates all others.
    shifted=S.shift(K); a=shifted.all_coeffs()[::-1];d=len(a)-1
    lhs=abs(int(a[0]))<<d
    rhs=sum(abs(int(c))<<(d-i) for i,c in enumerate(a[1:],1))
    assert lhs>rhs
    print('PASS exact root',K,'multiplicity',multiplicity,'isolation degree',d)
    print('dominance ratio >',lhs//max(rhs,1))
    print('wall_seconds',perf_counter()-start)
if __name__=='__main__':main()
