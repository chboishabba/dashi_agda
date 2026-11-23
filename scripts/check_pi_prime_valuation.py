"""Exact prime-exponent carry for Chudnovsky projective cross cancellation.

Classical Chudnovsky identity external; exact finite arithmetic only.
This benchmarks a predictive valuation carrier against math.gcd cross cancellation.
"""
from collections import Counter
from fractions import Fraction
from math import gcd, isqrt
from statistics import median
from time import perf_counter
import hashlib, sys

A,B,C=13591409,545140134,640320**3

def smallest_prime_factors(limit):
    spf=list(range(limit+1))
    for p in range(2,isqrt(limit)+1):
        if spf[p]==p:
            for x in range(p*p,limit+1,p):
                if spf[x]==x:spf[x]=p
    return spf

def factors(n,spf):
    n=abs(n); out=Counter()
    while n>1:
        p=spf[n];out[p]+=1;n//=p
    return out

def add(a,b):
    z=a.copy();z.update(b);return z

def value(a):
    v=1
    for p,e in a.items():v*=p**e
    return v

def splitter(spf):
    cf=Counter({prime:3*power for prime,power in factors(640320,spf).items()})
    ops=[0,0]
    def split(a,b,mode='valuation'):
        if a==b:return 1,1,0,Counter(),Counter()
        if b-a==1:
            if not a:return 1,1,A,Counter(),Counter()
            x=24*(2*a-1)*(6*a-5)*(6*a-1)
            y=C*a**3
            px=add(add(factors(24,spf),factors(2*a-1,spf)),add(factors(6*a-5,spf),factors(6*a-1,spf)))
            qx=add(cf,Counter({z:3*v for z,v in factors(a,spf).items()}))
            return -x,y,-x*(A+B*a),px,qx
        m=(a+b)//2
        p,q,t,pm,qm=split(a,m,mode)
        P,Q,T,PM,QM=split(m,b,mode)
        if mode=='valuation':
            inter=pm.keys()&QM.keys()
            shared={prime:min(pm[prime],QM[prime]) for prime in inter}
            g=value(shared)
            for prime,exponent in shared.items():
                pm[prime]-=exponent;QM[prime]-=exponent
                if not pm[prime]:del pm[prime]
                if not QM[prime]:del QM[prime]
            ops[0]+=1;ops[1]+=len(inter)
        else:
            g=gcd(p,Q)
        assert g>0
        p//=g;Q//=g
        if mode=='gcd':
            # No tracked maps for the baseline.
            return p*P,q*Q,t*Q+p*T,Counter(),Counter()
        return p*P,q*Q,t*Q+p*T,add(pm,PM),add(qm,QM)
    return split,ops

def base_split(a,b):
    if a==b:return 1,1,0
    if b-a==1:
        p,q=(1,1) if a==0 else (-24*(2*a-1)*(6*a-5)*(6*a-1),C*a**3)
        return p,q,(A+B*a)*p
    m=(a+b)//2
    p,q,t=base_split(a,m);P,Q,T=base_split(m,b)
    g=gcd(p,Q);p//=g;Q//=g
    return p*P,q*Q,t*Q+p*T

def calc(n,bits,mode,spf):
    if mode=='valuation':
        split,ops=splitter(spf)
        p,q,t,pm,qm=split(0,n)
    else:
        p,q,t=base_split(0,n);pm=qm=None;ops=None
    v=Fraction(t,q)
    nxt=Fraction(p,q)*Fraction(-24*(2*n-1)*(6*n-5)*(6*n-1),C*n**3)*(A+B*n)
    lo,hi=sorted((v,v+nxt))
    scale=1<<bits;root=isqrt(10005*scale*scale)
    L=Fraction(426880*root,scale)/hi
    U=Fraction(426880*(root+1),scale)/lo
    return (L,U),(p,q,t),(pm,qm),ops

def main():
    if hasattr(sys,'set_int_max_str_digits'):sys.set_int_max_str_digits(0)
    count=0
    for n in range(1,65):
        spf=smallest_prime_factors(max(640320,6*n))
        (a,b),z,(pm,qm),ops=calc(n,256,'valuation',spf)
        (c,d),w,_,_=calc(n,256,'gcd',spf)
        assert (a,b)==(c,d) and z==w
        assert value(pm)==abs(z[0]) and value(qm)==abs(z[1])
        count+=1
    print('PASS original cross-gcd exact triples and factor provenance',count,flush=True)
    for digits in (1000,10000,50000):
        n=digits//14+2;bits=4*digits+32
        spf=smallest_prime_factors(max(640320,6*n))
        rows=[];signature=None
        for mode in ('gcd','valuation'):
            times=[]
            for _ in range(3):
                start=perf_counter()
                (L,U),z,maps,ops=calc(n,bits,mode,spf)
                scale=10**digits
                x=L.numerator*scale//L.denominator
                y=U.numerator*scale//U.denominator
                assert x==y
                s=str(x)
                times.append((perf_counter()-start)*1000)
            if signature is None:signature=hashlib.sha256(s.encode()).hexdigest()
            else:assert signature==hashlib.sha256(s.encode()).hexdigest()
            if mode=='valuation':
                assert value(maps[0])==abs(z[0]) and value(maps[1])==abs(z[1])
            rows.append((mode,round(median(times),3),sum(abs(v).bit_length() for v in z),ops))
        print(digits,'terms',n,rows,'sha256',signature,flush=True)
if __name__=='__main__':main()
