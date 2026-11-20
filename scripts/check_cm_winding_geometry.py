"""Exact finite wheel/carry controls; classical quotient algebra.
Sweetgrass attribution is methodological, not mathematical authority.
"""
from itertools import product
from math import gcd
from sympy import Matrix, Poly, ZZ, eye, symbols, trace, zeros, mobius, divisors
from sympy.polys.matrices import DomainMatrix
from fractions import Fraction

def aggregate(x,M):
    # Word weights by length and total valuation, no word enumeration.
    a=[1]+[0]*M
    for k in range(1,M+1):
        b=[0]*(M+1)
        for i,c in enumerate(a):
            if c:
                for j,v in enumerate(x[1:M-i+1],1):b[i+j]+=c*v
        a=b
        yield k,a

def norm_aggregate(x,p,n):
    # q log derivative: k denominator cancels after marking a step.
    L=[Fraction(0)]*(n+1)
    for k,a in aggregate(x,p*n):
        for i in range(1,n+1):L[i]-=Fraction(p*i*a[p*i],k)
    N=[Fraction(1)]
    for i in range(1,n+1):N.append(sum(L[j]*N[i-j] for j in range(1,i+1))/i)
    assert all(v.denominator==1 for v in N)
    return list(map(int,N))

def main():
    q=symbols('q'); counts=[0,0,0,0]
    for p in (2,3,5,7,11,17,41):
        for r,s,u in product(range(p),repeat=3):
            assert (r+s)//p+((r+s)%p+u)//p==(s+u)//p+(r+(s+u)%p)//p
            counts[0]+=1
        for n in (1,2,3):
            M=p*n
            for i in range(M+1):
                j=(-i)%p
                assert i+j<=M and (i+j)%p==0
                counts[1]+=1
    for p in (2,3,4,5,6,7):
        T=zeros(p)
        for i in range(p-1):T[i+1,i]=1
        T[0,p-1]=q
        assert T**p==q*eye(p)
        for k in range(1,2*p+1):
            assert trace(T**k)==(p*q**(k//p) if k%p==0 else 0)
            counts[2]+=1
        for n in (1,2,3):
            for x in ([0,2,-3],[0,0,1,2],[0,-1,0,1]):
                H=eye(p)
                for j,c in enumerate(x):H-=c*T**j
                d=Poly(DomainMatrix.from_Matrix(H).det().as_expr(),q,domain=ZZ)
                assert norm_aggregate(x,p,n)==[int(d.nth(i)) for i in range(n+1)]
                counts[3]+=1
    print('PASS carry, reachability, trace, aggregate norm:',counts)
if __name__=='__main__':main()
