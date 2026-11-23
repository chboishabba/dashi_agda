#!/usr/bin/env python3
"""COMP4: ordered Chudnovsky product-tree shapes with pre-multiplication GCD.

Exact finite rational and decimal-floor tests; the classical Chudnovsky
identity and original Bishop same-real theorem are external obligations.
"""
from bisect import bisect_left
from fractions import Fraction
from math import gcd, isqrt, log2
from statistics import median
from time import perf_counter
from hashlib import sha256
import sys

A,B,C=13591409,545140134,640320**3

class Stats:
    def __init__(self):
        self.merges=0;self.cancel=0;self.maxbits=0;self.work=0;self.depth=0
    def observe(self,a,b,c,A,B,C,dep):
        self.merges+=1
        self.maxbits=max(self.maxbits,*[abs(x).bit_length() for x in (a,b,c,A,B,C)])
        self.work+=a.bit_length()*A.bit_length()+b.bit_length()*B.bit_length()+c.bit_length()*B.bit_length()+a.bit_length()*C.bit_length()
        self.depth=max(self.depth,dep)

def weights(n):
    w=[0.0]
    for k in range(n):w.append(w[-1]+log2(C)+3*log2(max(k,1)))
    return w

def midpoint(a,b,shape,w):
    if shape=='half':return (a+b)//2
    if shape=='quarter':return a+max(1,(b-a)//4)
    if shape=='threequarter':return a+max(1,3*(b-a)//4)
    if shape=='weighted':
        m=bisect_left(w,(w[a]+w[b])/2,a+1,b)
        return max(a+1,min(b-1,m))
    raise ValueError(shape)

def split(a,b,shape,w,stats=None,depth=0):
    if a==b:return 1,1,0
    if b-a==1:
        p,q=(1,1) if a==0 else (-24*(2*a-1)*(6*a-5)*(6*a-1),C*a**3)
        return p,q,(A+B*a)*p
    m=midpoint(a,b,shape,w)
    p,q,t=split(a,m,shape,w,stats,depth+1)
    P,Q,T=split(m,b,shape,w,stats,depth+1)
    g=gcd(p,Q);p//=g;Q//=g
    if stats is not None:
        stats.cancel+=(g>1)
        stats.observe(p,q,t,P,Q,T,depth)
    return p*P,q*Q,t*Q+p*T

def interval(n,bits,shape,w):
    p,q,t=split(0,n,shape,w)
    v=Fraction(t,q)
    nxt=Fraction(p,q)*Fraction(-24*(2*n-1)*(6*n-5)*(6*n-1),C*n**3)*(A+B*n)
    lo,hi=sorted((v,v+nxt))
    assert lo>0
    s=1<<bits;z=isqrt(10005*s*s)
    return Fraction(426880*z,s)/hi,Fraction(426880*(z+1),s)/lo

def certify(d,shape,w):
    n=d//14+2;bits=4*d+32
    lo,hi=interval(n,bits,shape,w)
    scale=10**d
    x=lo.numerator*scale//lo.denominator
    y=hi.numerator*scale//hi.denominator
    assert x==y
    return str(x)

def main():
    if hasattr(sys,'set_int_max_str_digits'):sys.set_int_max_str_digits(0)
    shapes=('half','weighted','quarter','threequarter')
    count=0
    for a in range(12):
        for b in range(a,a+17):
            w=weights(b);p,q,t=split(a,b,'half',w)
            for shape in shapes[1:]:
                P,Q,T=split(a,b,shape,w)
                assert p*Q==P*q and t*Q==T*q
                count+=1
    print('EXACT_SUBINTERVALS',count,flush=True)
    for d in (1000,10000,50000):
        n=d//14+2;w=weights(n)
        outputs=[];rows=[]
        for shape in shapes:
            samples=[]
            for _ in range(3):
                start=perf_counter();s=certify(d,shape,w)
                samples.append((perf_counter()-start)*1000)
            outputs.append(s)
            stats=Stats();p,q,t=split(0,n,shape,w,stats)
            rows.append((shape,round(median(samples),3),
                         sum(abs(x).bit_length() for x in (p,q,t)),
                         stats.depth,stats.maxbits,stats.cancel,stats.work))
        assert all(s==outputs[0] for s in outputs)
        print('DIGITS',d,'HASH',sha256(outputs[0].encode()).hexdigest(),flush=True)
        for row in rows:print('RESULT',row,flush=True)

if __name__=='__main__':main()
