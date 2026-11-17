#!/usr/bin/env python3
"""Exact test of atan(1/5)=atan(1/8)+atan(3/41).

Finite rational reference; equality of original Bishop arctangent limits
still requires the original same-source analytic addition/branch theorem.
Attribution: Machin; Bishop/Bridges; Murray/Csimma; DASHI original
BishopMachinArctanConstructionExact and tangent algebra.
"""
from fractions import Fraction as F
from statistics import median
from time import perf_counter
from check_bishop_fast_pi_binary_split import atan_split, schedule, MACHIN, enclosure

SPLIT_FORMULA=((16,1,8),(16,3,41),(-4,1,239))

def tree(term,a,b):
    if a>=b:return 1,1,0
    if b-a==1:
        p,q=term(a)
        return p,q,p
    m=(a+b)//2
    p1,q1,t1=tree(term,a,m)
    p2,q2,t2=tree(term,m,b)
    return p1*p2,q1*q2,t1*q2+p1*t2

def atan_rational(p,q,n):
    if n==0:return F(0)
    _,d,t=tree(lambda k:(p,q) if k==0 else (-(2*k-1)*p*p,(2*k+1)*q*q),0,n)
    return F(t,d)

def atan_power_two(q,n):
    assert q>0 and (q&(q-1))==0
    if n==0:return F(0)
    shift=q.bit_length()-1
    def run(a,b):
        if a>=b:return (1,1,0,0)
        if b-a==1:
            p=1 if a==0 else -(2*a-1)
            odd=1 if a==0 else 2*a+1
            return p,odd,p,shift if a==0 else 2*shift
        m=(a+b)//2
        p1,q1,t1,e1=run(a,m);p2,q2,t2,e2=run(m,b)
        return p1*p2,q1*q2,(t1*q2<<e2)+p1*t2,e1+e2
    _,odd,t,e=run(0,n)
    return F(t,odd<<e)

def cutoff(c,p,q,digits,parts):
    n=0;power=p;den=q;target=10**digits
    while abs(c)*parts*target*power>(2*n+1)*den:
        n+=1;power*=p*p;den*=q*q
    return n

def interval(p,q,n,shift=False):
    v=atan_power_two(q,n) if shift else atan_rational(p,q,n)
    next_term=F((-1)**n*p**(2*n+1),(2*n+1)*q**(2*n+1))
    return min(v,v+next_term),max(v,v+next_term)

def split_enclosure(digits):
    ns=[cutoff(c,p,q,digits,len(SPLIT_FORMULA)) for c,p,q in SPLIT_FORMULA]
    lo=hi=F(0)
    for (c,p,q),n in zip(SPLIT_FORMULA,ns):
        a,b=interval(p,q,n,q==8)
        if c>=0:lo+=c*a;hi+=c*b
        else:lo+=c*b;hi+=c*a
    assert 0<=hi-lo<=F(1,10**digits)
    return ns,lo,hi

def check():
    a,b=F(1,8),F(3,41)
    assert (a+b)/(1-a*b)==F(1,5)
    for q in (8,16,32,64):
        for n in range(35):
            assert atan_power_two(q,n)==atan_rational(1,q,n)
    for p,q in ((3,41),(1,5),(1,239)):
        for n in range(20):
            direct=sum((F((-1)**k*p**(2*k+1),(2*k+1)*q**(2*k+1))
                        for k in range(n)),F(0))
            assert atan_rational(p,q,n)==direct
    for d in (50,100,1000):
        ns= schedule(MACHIN,d)
        a,b=enclosure(MACHIN,ns)
        _,c,e=split_enclosure(d)
        assert a<=e and c<=b
    print("PASS exact tangent addition, shifted tree parity, and finite interval intersections")
def bench():
    check()
    for d in (100,1000,3000,10000):
        original_ns=schedule(MACHIN,d)
        split_ns=[cutoff(c,p,q,d,len(SPLIT_FORMULA)) for c,p,q in SPLIT_FORMULA]
        variants=(
            ("original",lambda:[atan_split(q,n) for (_,q),n in zip(MACHIN,original_ns)]),
            ("decomposed",lambda:[atan_rational(p,q,n) for (_,p,q),n in zip(SPLIT_FORMULA,split_ns)]),
            ("shifted",lambda:[atan_power_two(q,n) if q==8 else atan_rational(p,q,n)
                               for (_,p,q),n in zip(SPLIT_FORMULA,split_ns)]))
        result={}
        for name,fn in variants:
            times=[]
            for _ in range(7):
                t=perf_counter();fn();times.append(1000*(perf_counter()-t))
            result[name]=round(median(times),3)
        print(d,"terms",sum(original_ns),sum(split_ns),"median_ms",result)

if __name__=="__main__":bench()
