#!/usr/bin/env python3
"""RH-to-Pi geometry: reversible weighted atlas, ordered product no-go.

This is an analogy of the exact q^-6 -> u dyadic geometry, NOT an RH
zero theorem, group action, or measured speedup.
"""
from fractions import Fraction
from bisect import bisect_right
from math import gcd

C=640320**3; A=13591409; B=545140134; N=1<<15

def leaves(n):
    for k in range(n):
        p,q=(1,1) if not k else (-24*(2*k-1)*(6*k-5)*(6*k-1),C*k**3)
        yield p,q,(A+B*k)*p

def compose(l,r):
    p,q,t=l;P,Q,T=r
    return p*P,q*Q,t*Q+p*T

def chart(weights,i,theta=Fraction(0)):
    assert 0<=i<len(weights) and 0<=theta<1
    prefix=sum(weights[:i]); total=sum(weights)
    u=(prefix+theta*weights[i])/total
    return int(N*u),N*u-int(N*u)

def inverse(weights,k,theta):
    assert 0<=k<N and 0<=theta<1
    W=sum(weights);cum=[0]
    for w in weights:cum.append(cum[-1]+w)
    value=Fraction(W*(k+theta),N)
    j=min(len(weights)-1,bisect_right(cum,value)-1)
    return j,(value-cum[j])/weights[j]

def main():
    # Exact geometric atlas and inverse with residual retained.
    count=0
    for n in (2,3,7,16,31,64):
        weights=[abs(p).bit_length()+q.bit_length() for p,q,_ in leaves(n)]
        for i in range(n):
            for theta in (Fraction(0),Fraction(1,3),Fraction(2,3),Fraction(999,1000)):
                k,r=chart(weights,i,theta)
                ii,tt=inverse(weights,k,r)
                assert (ii,tt)==(i,theta)
                count+=1
    print('PASS exact atlas and inverse',count)
    l,r=list(leaves(3))[1:]
    forward=compose(l,r);backward=compose(r,l)
    assert Fraction(forward[2],forward[1])!=Fraction(backward[2],backward[1])
    assert forward[2]*backward[1]!=backward[2]*forward[1]
    print('PASS noncommutativity (reordering is invalid)')
    # At 1M decimal places > 2^15 leaves: 15 bits alone cannot recover leaf.
    n=1000000//14+2
    weights=[abs(p).bit_length()+q.bit_length() for p,q,_ in leaves(n)]
    total=sum(weights); prefix=0;seen=set();collisions=0
    for w in weights:
        k=N*prefix//total
        if k in seen:collisions+=1
        seen.add(k);prefix+=w
    assert len(seen)==N and collisions==n-N==38662
    print('PASS 15-bit atlas collision negative control',n,len(seen),collisions)
if __name__=='__main__':main()
