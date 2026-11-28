#!/usr/bin/env python3
"""Selective small-prime valuation + residual GCD for exact Chudnovsky splitting.

Reuse projective triple and certified-floor consumers. Only controlled arithmetic
is asserted; the classical Chudnovsky identity remains an external premise.
"""
from fractions import Fraction
from math import gcd, isqrt
from statistics import median
from time import perf_counter
import hashlib
import sys

A, B, C = 13591409, 545140134, 640320**3

def small_primes(bound):
    sieve = bytearray(b'\x01') * (bound + 1)
    sieve[:2] = b'\x00\x00'
    for p in range(2, isqrt(bound) + 1):
        if sieve[p]:
            sieve[p*p:bound+1:p] = b'\x00' * (((bound-p*p)//p)+1)
    return tuple(i for i in range(2, bound+1) if sieve[i])

def leaf_valuations(k, primes):
    if k == 0:
        return (0,) * len(primes), (0,) * len(primes)
    pn = 24 * (2*k-1) * (6*k-5) * (6*k-1)
    qn = C * k**3
    vp, vq = [], []
    for prime in primes:
        a,b = pn,qn
        ap = bp = 0
        while a % prime == 0:
            a //= prime
            ap += 1
        while b % prime == 0:
            b //= prime
            bp += 1
        vp.append(ap)
        vq.append(bp)
    return tuple(vp), tuple(vq)

def split(a,b,mode='gcd',primes=(),stats=None):
    if a==b:return (1,1,0), ((0,)*len(primes),(0,)*len(primes))
    if b-a==1:
        p,q = (1,1) if a==0 else (-24*(2*a-1)*(6*a-5)*(6*a-1), C*a**3)
        return (p,q,(A+B*a)*p), leaf_valuations(a,primes) if mode == 'selective' else ((),())
    mid=(a+b)//2
    (p,q,t),(lp,lq)=split(a,mid,mode,primes,stats)
    (P,Q,T),(rp,rq)=split(mid,b,mode,primes,stats)
    if mode=='selective':
        shared=tuple(min(x,y) for x,y in zip(lp,rq))
        smooth=1
        for prime,e in zip(primes,shared):
            if e:smooth *= prime**e
        assert p % smooth == 0 and Q % smooth == 0
        p//=smooth;Q//=smooth
        leftover=gcd(p,Q)
        if stats is not None:
            stats[0] += 1
            stats[1] += (smooth>1)
            stats[2] += (leftover>1)
            stats[3] += smooth.bit_length()
        # The leftover has no factor among the tracked primes.
        p//=leftover;Q//=leftover
        emap=(tuple(x-z+y for x,z,y in zip(lp,shared,rp)),
              tuple(x+y-z for x,y,z in zip(lq,rq,shared)))
    else:
        common=gcd(p,Q)
        p//=common;Q//=common
        emap=((),())
    return (p*P,q*Q,t*Q+p*T),emap

def interval(n,bits,mode,primes=(),stats=None):
    (p,q,t),maps=split(0,n,mode,primes,stats)
    v=Fraction(t,q)
    nxt=Fraction(p,q)*Fraction(-24*(2*n-1)*(6*n-5)*(6*n-1),C*n**3)*(A+B*n)
    lo,hi=sorted((v,v+nxt))
    scale=1<<bits
    z=isqrt(10005*scale**2)
    return (Fraction(426880*z,scale)/hi,Fraction(426880*(z+1),scale)/lo),(p,q,t),maps

def certified(d,mode,primes=(),stats=None):
    n=d//14+2
    bits=4*d+32
    scale=10**d
    while True:
        (lo,hi),triple,maps=interval(n,bits,mode,primes,stats)
        x=(lo.numerator*scale)//lo.denominator
        y=(hi.numerator*scale)//hi.denominator
        if x==y:
            return str(x),triple,maps,n,bits
        n+=max(1,n//16)
        bits+=max(32,bits//16)

def main():
    if hasattr(sys,'set_int_max_str_digits'):sys.set_int_max_str_digits(0)
    results=[]
    tests=0
    for limit in (2,7,31,127):
        primes=small_primes(limit)
        for a in range(16):
            for length in (0,1,2,3,4,8,16):
                z,_=split(a,a+length,'gcd')
                v,m=split(a,a+length,'selective',primes)
                assert z==v,(a,length,limit)
                for i,component in enumerate((v[0],v[1])):
                    for prime,e in zip(primes,m[i]):
                        actual=0;component=abs(component)
                        while component and component%prime==0:
                            component//=prime;actual+=1
                        assert e==actual,(a,length,prime,e,actual)
                tests+=1
    print('PASS interval triple and selected valuation invariants',tests,flush=True)
    for digits in (1000,10000,50000):
        reference=None
        for mode,limit in (('gcd',0),('selective',7),('selective',31),('selective',127)):
            primes=small_primes(limit) if limit else ()
            samples=[];stats=[0,0,0,0]
            for _ in range(3):
                start=perf_counter()
                s,z,maps,n,bits=certified(digits,mode,primes,stats)
                samples.append((perf_counter()-start)*1000)
            if reference is None:reference=s
            else:assert s==reference
            results.append((digits,mode,limit,round(median(samples),3),
                            sum(abs(x).bit_length() for x in z),n,tuple(stats)))
            print('BENCH',results[-1],flush=True)
        print('HASH',digits,hashlib.sha256(reference.encode()).hexdigest(),flush=True)
    assert len(results)==12

if __name__=='__main__':main()
