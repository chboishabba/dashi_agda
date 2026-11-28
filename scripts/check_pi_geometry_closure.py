#!/usr/bin/env python3
"""Original Machin/Chudnovsky strict common floor and predictive-join trace.
Exact finite arithmetic; not an all-index analytic or kernel proof.
"""
import argparse, hashlib, json, sys
from fractions import Fraction as F
from math import gcd, isqrt
from pathlib import Path
from time import monotonic
from check_chudnovsky_bishop_semantics import machin
from check_chudnovsky_exact import interval,A,B,C
from check_pi_prime_valuation import smallest_prime_factors, factors
from collections import Counter

def leaf(k):
    p,q=(1,1) if k==0 else (-24*(2*k-1)*(6*k-5)*(6*k-1), C*k**3)
    return p,q,p*(A+B*k)

def join(l,r):
    p,q,t=l; P,Q,T=r
    return p*P,q*Q,t*Q+p*T

def ledger_split(a,b,spf,trace=False):
    if a==b: return (1,1,0),Counter(),Counter(),["empty"]
    if b-a==1:
        p,q,t=leaf(a)
        pm=Counter();qm=Counter()
        if a:
            for x in (24,2*a-1,6*a-5,6*a-1): pm.update(factors(x,spf))
            qm.update({p:3*v for p,v in factors(640320,spf).items()})
            qm.update({p:3*v for p,v in factors(a,spf).items()})
        return (p,q,t),pm,qm,["leaf",a] if trace else None
    m=(a+b)//2
    l,lp,lq,lt=ledger_split(a,m,spf,trace)
    r,rp,rq,rt=ledger_split(m,b,spf,trace)
    shared=lp & rq
    g=1
    for p,e in shared.items(): g*=p**e
    p,q,t=l; P,Q,T=r
    pp,pr=divmod(p,g); qq,qr=divmod(Q,g)
    assert g>0 and pr==qr==0 and qq>0
    assert g==gcd(p,Q)
    out=join((pp,q,t),(P,qq,T))
    return out,(lp-shared)+rp,lq+(rq-shared),["merge",lt,rt,str(g),str(qq),str(pp)] if trace else None

def replay(t):
    if t[0]=="empty": return (1,1,0),[]
    if t[0]=="leaf": return leaf(t[1]),[t[1]]
    _,lt,rt,g,rq,lp=t
    l,ls=replay(lt);r,rs=replay(rt)
    g,rq,lp=map(int,(g,rq,lp))
    assert g>0 and rq>0 and l[0]==g*lp and r[1]==g*rq
    return join((lp,l[1],l[2]),(r[0],rq,r[2])),ls+rs

def floor_gate(L,U,d):
    s=10**d
    assert 0<L<=U
    x=L.numerator*s//L.denominator
    if U.numerator*s >= (x+1)*U.denominator: return None
    assert x*L.denominator<=L.numerator*s
    return x

def common(d,trace_path=None):
    n=d//14+2;bits=4*d+32
    m=max(1,3*d//4);k=max(1,d//4)
    for attempt in range(12):
        L,U=interval(n,bits);l,u=machin(m,k)
        x=floor_gate(L,U,d);y=floor_gate(l,u,d)
        if x is not None and y is not None:
            assert x==y and max(L,l)<=min(U,u)
            break
        n+=max(1,n//8);bits+=max(32,bits//8)
        m+=max(1,m//8);k+=max(1,k//8)
    else: raise RuntimeError("no common floor admitted")
    result={"digits":d,"sha256":hashlib.sha256(str(x).encode()).hexdigest(),"chudnovsky_terms":n,"machin_terms":[m,k],"bits":bits,"attempts":attempt+1}
    if trace_path:
        z,pm,qm,t=ledger_split(0,n,smallest_prime_factors(max(640320,6*n)),True)
        w,indices=replay(t)
        assert z==w and indices==list(range(n))
        for v,mp in zip(z[:2],(pm,qm)):
            prod=1
            for p,e in mp.items():prod*=p**e
            assert prod==abs(v)
        p,q,T=z;P,Q,T1=leaf(n)
        a,b=sorted((F(T,q),F(T*Q+p*T1,q*Q)))
        scale=1<<bits;r=isqrt(10005*scale**2)
        assert r*r<=10005*scale**2<(r+1)**2
        assert floor_gate(F(426880*r,scale)/b,F(426880*(r+1),scale)/a,d)==x
        Path(trace_path).write_text(json.dumps({"tree":t,"receipt":{"digits":d,"n":n,"r":str(r),"scale":str(scale),"x":str(x)}})+"\n")
        result["trace_replay"]=True
    return result

if __name__=="__main__":
    sys.set_int_max_str_digits(0)
    ap=argparse.ArgumentParser();ap.add_argument("digits",type=int);ap.add_argument("--trace")
    a=ap.parse_args();assert a.digits>0
    start=monotonic();result=common(a.digits,a.trace);result["seconds"]=monotonic()-start
    print(json.dumps(result),flush=True)
