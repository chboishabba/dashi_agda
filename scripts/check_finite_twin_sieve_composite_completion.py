#!/usr/bin/env python3
"""Construct BOTH composite endpoints surviving each tested finite prime sieve.

Finite exact CRT, source roots: Chinese remainder theorem, Eratosthenes,
Brun's local prime-pair sieve. Executable countermodel, not a proof of
twin-prime infinitude or an Agda kernel receipt.
"""
from math import gcd, isqrt, prod

SSP15=(2,3,5,7,11,13,17,19,23,29,31,41,47,59,71)

def prime(n):
    return n>=2 and all(n%d for d in range(2,isqrt(n)+1))

def nextprime(n):
    n+=1
    while not prime(n): n+=1
    return n

def survivor(n,axes):
    return all(n%p and (n+2)%p for p in axes)

def merge(r,M,t,p):
    assert gcd(M,p)==1
    q=(r+M*(((t-r)*pow(M,-1,p))%p))
    assert q%M==r and q%p==t and 0<=q<M*p
    return q

def certify(axes):
    axes=tuple(sorted(set(axes)))
    assert all(prime(p) for p in axes)
    P=prod(axes)
    r=next(n for n in range(1,2000) if survivor(n,axes))
    q1=nextprime(max(axes,default=2))
    q2=nextprime(q1)
    assert q1 not in axes and q2 not in axes
    a=merge(r,P,0,q1)
    b=merge(a,P*q1,(-2)%q2,q2)
    n=b+P*q1*q2
    assert survivor(n,axes)
    assert n%q1==0 and (n+2)%q2==0
    assert n>q1 and n+2>q2
    assert n%P==r%P
    for k in (1,2,3,10,53):
        candidate=b+k*P*q1*q2
        assert survivor(candidate,axes)
        assert candidate%q1==0 and (candidate+2)%q2==0
        assert candidate>q1 and candidate+2>q2
    print(f'axes={len(axes):2}, r={r}, p1={q1}, p2={q2}, period={P}, '
          f'double-composite start={n}')

def main():
    for axes in ((2,3),(2,3,5,7),(2,3,5,7,11,13),SSP15,
                 (2,3,5,7,11,13,37,43)):
        certify(axes)
    print('Finite sieve double-composite CRT construction: PASS')
    print('No unbounded prime theorem. Assumes classical CRT in this Python implementation.')

if __name__=='__main__': main()
