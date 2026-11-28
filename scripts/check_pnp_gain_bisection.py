"""Localize an original verified 0->1 pin gain without monotonicity.
The missed original witness is a premise, not produced universally.
Candidate is a fixed deterministic clocked producer on each pinned CNF.
"""
from check_p0_signed_contrast_20261125 import ContinuationAllowance
from check_pnp_endpoint_portfolio import cnf_solver


def bisect_gain(n,score):
    if n<1:raise ValueError('nontrivial interval')
    a,b=0,n
    # The endpoint scores are evaluated by the caller or provided by its
    # verified cache. No monotonicity assumption is used.
    if score(a) or not score(b):return None
    while b-a>1:
        m=(a+b)//2
        if score(m):b=m
        else:a=m
    return a,b


def valid(F,n,x):
    return x is not None and len(x)==n and all(b in (0,1) for b in x) and all(any(x[abs(l)-1]==int(l>0) for l in c) for c in F)


def localize(F,n,w,producer,per_call,root):
    if n<0 or any(not 1<=abs(l)<=n for c in F for l in c) or not valid(F,n,w):raise ValueError('original witness')
    pins=tuple(((i+1)*(2*b-1),) for i,b in enumerate(w));cache={}
    class Refused(Exception):pass
    def score(i):
        if i in cache:return cache[i][0]
        # Charge actual prefix construction and candidate's full share,
        # including a failed attempt. Fully pinned anchor is explicit.
        setup=1+n+sum(1+len(c) for c in F)+2*i
        if not root.reserve('gain_setup',setup):raise Refused()
        G=F+pins[:i]
        if i==n:x=w
        else:
            if not root.reserve('gain_candidate',per_call):raise Refused()
            x=producer(G,n,per_call).get('witness')
        ok=valid(G,n,x);cache[i]=(ok,x if ok else None);return ok
    try:
        edge=bisect_gain(n,score) if n else None
    except Refused:return dict(status='UNKNOWN',queries=len(cache))
    if edge is None:return dict(status='ROOT_VERIFIED',queries=len(cache))
    a,b=edge
    assert b==a+1 and not cache[a][0] and cache[b][0]
    return dict(status='GAIN',prefix=a,literal=pins[a][0],parent=F+pins[:a],child=F+pins[:b],witness=cache[b][1],queries=len(cache))


def main():
    from itertools import product
    from random import Random
    checks=0
    for n in range(1,13):
        for mid in product((False,True),repeat=n-1):
            S=(False,)+mid+(True,);calls=[]
            def score(i):calls.append(i);return S[i]
            a,b=bisect_gain(n,score);assert not S[a] and S[b] and b==a+1
            assert len(calls)<=2+(n-1).bit_length();checks+=1
    # Actual bounded solver, not a mocked score, evaluated on every
    # queried original pinned CNF. Use explicit known original witnesses.
    rng=Random(3693003);gains=0;complete=0
    for n in range(2,13):
        for _ in range(10):
            w=tuple(rng.randrange(2) for i in range(n))
            F=tuple(((i+1)*(2*b-1),) for i,b in enumerate(w))
            for cap in (0,100000):
                root=ContinuationAllowance(10000000)
                q=localize(F,n,w,lambda G,m,a:cnf_solver(G,m,(),(),a),cap,root)
                if cap==0:
                    assert q['status']=='GAIN' and valid(q['child'],n,q['witness'])
                    assert q['queries']<=2+(n-1).bit_length();gains+=1
                else:assert q['status']=='ROOT_VERIFIED';complete+=1
    # Independent positive-budget controls, genuinely successful before
    # the fully-pinned override. Witness used only to specify the path.
    rng=Random(123);interior=0
    for _ in range(25):
        n=6;w=tuple(rng.randrange(2) for i in range(n));F=[]
        for j in range(2*n):
            c=tuple(rng.choice((-1,1))*(v+1) for v in rng.sample(range(n),3))
            if not any(w[abs(l)-1]==int(l>0) for l in c):c=(-c[0],)+c[1:]
            F.append(c)
        F=tuple(F)
        for cap in (500,1000,2000,4000):
            q=localize(F,n,w,lambda G,n,c:cnf_solver(G,n,(),(),c),cap,ContinuationAllowance(1000000))
            if q['status']=='GAIN' and q['prefix']+1<n:
                assert valid(q['child'],n,q['witness']);interior+=1;break
    assert interior>0
    q=localize(((1,),),1,(1,),lambda G,n,c:cnf_solver(G,n,(),(),c),0,ContinuationAllowance(0));assert q['status']=='UNKNOWN' 
    print(dict(nonmonotone_paths=checks,actual_gains=gains,already_verified=complete,interior_gains=interior,refusal=1))
if __name__=='__main__':main()
