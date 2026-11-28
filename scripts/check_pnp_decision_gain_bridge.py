"""Decision-derived original witness path and verified failure receipt.
The search uses only the candidate's answers; the reference truth
verifier is used only after an actual gain, and need not be polynomial.
"""
from itertools import product
from check_pnp_fixed_code_gain import Candidate,localize,verify,valid
from check_p0_signed_contrast_20261125 import ContinuationAllowance
from check_pnp_endpoint_live_fold import solve as live


def search(F,n,decision):
    G=F;x=[];queries=[]
    for i in range(1,n+1):
        q=G+((-i,),);a=bool(decision(q,n));queries.append((q,a))
        b=int(not a);x.append(b);G+=((i*(2*b-1),),)
    x=tuple(x)
    return dict(witness=x if valid(F,n,x) else None,queries=tuple(queries),terminal=x)


def extract(F,n,decision,w):
    if not valid(F,n,w):raise ValueError('missed-source witness')
    q=search(F,n,decision)
    if q['witness'] is not None:return None
    for G,a in q['queries']:
        y=next((x for x in product((0,1),repeat=n) if valid(G,n,x)),None)
        if a!=(y is not None):return dict(formula=G,answer=a,witness=y,queries=q['queries'])
    raise AssertionError('miss with no query error')


def main():
    from random import Random
    from collections import Counter
    rng=Random(3693203);C=Counter()
    def exact(F,n):return any(valid(F,n,x) for x in product((0,1),repeat=n))
    deciders=(lambda F,n:True,lambda F,n:False,lambda F,n:sum(sum(c) for c in F)%3==0,lambda F,n:live(F,n,(),(),(),128)['status']=='WITNESS',exact)
    for n in range(1,7):
        for _ in range(32):
            w=tuple(rng.randrange(2) for i in range(n));F=[]
            for j in range(2*n):
                c=tuple(rng.choice((-1,1))*rng.randrange(1,n+1) for _ in range(3))
                if not any(w[abs(l)-1]==int(l>0) for l in c):c=(-c[0],)+c[1:]
                F.append(c)
            F=tuple(F)
            for d in deciders:
                q=search(F,n,d);assert len(q['queries'])==n
                z=extract(F,n,d,w)
                if q['witness'] is not None:assert z is None and valid(F,n,q['witness']);C['verified']+=1
                else:
                    assert (z['formula'],z['answer']) in q['queries'] and d(z['formula'],n)==z['answer']
                    assert z['answer']!=exact(z['formula'],n);C['failure']+=1
                    e=Candidate(lambda G,m,a:search(G,m,d),lambda G,m:1+m*sum(1+len(c) for c in G))
                    g=localize(F,n,w,e,ContinuationAllowance(10**7))
                    assert verify(e,g)
                    zz=extract(g['parent'],n,d,g['witness']);assert zz is not None and zz['answer']!=exact(zz['formula'],n)
                    C['gain_to_failure']+=1
                if d is exact:assert q['witness'] is not None
    print(dict(C))
if __name__=='__main__':main()
