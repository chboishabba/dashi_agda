#!/usr/bin/env python3
"""Executable rational bridge; analytic inputs are documented in roadmap.
No Agda/Lean kernel claim. Reuses original Chudnovsky interval evaluator.
"""
from fractions import Fraction as F
from time import perf_counter
from sympy import I, expand, symbols, Poly, ZZ
from check_chudnovsky_exact import interval, A, B, C


def ramanujan_prefix(n):
    q = symbols('q')
    s = [[0]*(n+1) for _ in range(3)]
    for d in range(1,n+1):
        for k in range(d,n+1,d):
            for j,power in enumerate((1,3,5)):
                s[j][k] += d**power
    e,a,b = [Poly.from_list(([1]+[scale*v for v in seq[1:]])[::-1],q,domain=ZZ)
             for scale,seq in zip((-24,240,-504),s)]
    D=lambda f: f.diff()*Poly(q,q)
    residuals=(12*D(e)-e*e+a,3*D(a)-e*a+b,2*D(b)-e*b+a*a)
    for r in residuals:
        assert all(r.nth(k)==0 for k in range(n+1))
    return 3*(n+1)


def atan_split(q,a,b):
    if b-a==1:
        p,d=(- (2*a-1), (2*a+1)*q*q) if a else (1,q)
        return p,d,p
    m=(a+b)//2
    p,d,t=atan_split(q,a,m); P,D,T=atan_split(q,m,b)
    return p*P,d*D,t*D+p*T


def atan_bracket(q,n):
    p,d,t=atan_split(q,0,n)
    v=F(t,d)
    nxt=F(p,d)*F(-(2*n-1),(2*n+1)*q*q)
    return min(v,v+nxt),max(v,v+nxt)


def machin(n,m):
    a,b=atan_bracket(5,n); c,d=atan_bracket(239,m)
    return 16*a-4*d,16*b-4*c


def certificate(digits):
    eps=F(1,10**digits)
    n=max(1,digits*3//4); m=max(1,digits//4)
    st=perf_counter()
    while True:
        l,u=machin(n,m)
        if u-l<=eps:break
        n+=max(1,n//8);m+=max(1,m//8)
    tm=perf_counter()-st
    k=digits//14+2; bits=4*digits+32
    st=perf_counter()
    while True:
        L,U=interval(k,bits)
        if U-L<=eps:break
        k*=2;bits*=2
    tc=perf_counter()-st
    assert max(l,L)<=min(u,U)
    assert max(u,U)-min(l,L)<=2*eps
    return n+m,k,tm,tc


def main():
    assert expand((5+I)**4*(239-I)-I*(5-I)**4*(239+I))==0
    r=ramanujan_prefix(256)
    print('PASS Gaussian Machin identity;',r,'Ramanujan coefficient identities')
    assert A+B<42*A and 42*1728<C
    assert 426880**2*10005*144==640320**3
    for digits in (100,1000,3000,10000):
        n,k,tm,tc=certificate(digits)
        print(digits,n,k,round(tm*1000,3),round(tc*1000,3),'PASS',flush=True)

if __name__=='__main__':main()
