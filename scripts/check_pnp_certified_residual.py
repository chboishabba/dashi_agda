"""Bounded original-source trichotomy; refusal is not an irreducibility proof."""
from itertools import product,combinations
from check_pnp_source_derived_cover import Reservation,Refused,source_cover
from check_p0_signed_contrast_20261125 import ContinuationAllowance
from check_pnp_prime_power_incidence import contradiction,verify,solve as modular
from check_pnp_frontier_resolution import accepts,norm
from check_pnp_affine_normal_components import canon,chart
from check_pnp_hall_geometry import cnf_solver as prior
from check_pnp_endpoint_live_fold import solve as live


def xor_clauses(ids,b):
    return tuple(tuple((i+1)*(1-2*x) for i,x in zip(ids,v)) for v in product((0,1),repeat=len(ids)) if sum(v)%2!=b)


def parity(F,n,B):
    B.pay(1+n+sum(1+len(c) for c in F));D=set(map(norm,F));scopes=set()
    for c in D:
        ids=tuple(sorted({abs(l)-1 for l in c}))
        if 1<=len(ids)==len(c)<=4:scopes.add(ids)
    H=[]
    for ids in sorted(scopes):
        B.pay(1+2**len(ids)*(1+len(ids)))
        for b in (0,1):
            if all(norm(c) in D for c in xor_clauses(ids,b)):H.append((ids,b))
    B.pay(1+len(H)*(n+1));A=tuple(tuple(int(i in ids) for i in range(n)) for ids,b in H);t=tuple(b for ids,b in H)
    z=contradiction(A,t,n,2,1,B)
    if z is not None:
        assert verify(A,t,n,2,z['weights']);return dict(status='EMPTY',rows=H,certificate=z,route='xor')
    B.pay(1+(n+1)*(len(H)+1)**2)
    R=canon((sum(1<<i for i in ids),b) for ids,b in H);assert R is not None
    u,V=chart(n,R);return dict(status='RESIDUAL',rows=H,witness=tuple(u>>i&1 for i in range(n)),rank=len(R))


def valid(F,n,A,t,O,x):
    return len(x)==n and all(b in (0,1) for b in x) and accepts(F,x) and all(sum(a*b for a,b in zip(row,x))%3==v%3 for row,v in zip(A,t)) and all(sum(x[i] for i in c)==1 for c in O)


def dispatch(F,n,A,t,O,cap):
    if n<0 or any(not 1<=abs(l)<=n for c in F for l in c) or len(A)!=len(t) or any(len(row)!=n for row in A) or any(len(set(c))!=len(c) or any(not 0<=i<n for i in c) for c in O):raise ValueError('source')
    root=ContinuationAllowance(cap);attempts=[];size=1+n+sum(1+len(c) for c in F)+len(A)*(n+1)+sum(1+len(c) for c in O)
    def result(q):
        assert sum(root.charges.values())+root.left==cap
        return dict(q,attempts=tuple(attempts),charges=dict(root.charges),reserved=cap-root.left)
    def witness(q):return q.get('witness') is not None and valid(F,n,A,t,O,q['witness'])
    if not root.reserve('source_audit',size):return result(dict(status='UNKNOWN',source=(F,n,A,t,O),reason='source_budget'))
    base=root.left;part=base//8
    assert root.reserve('parity',part);B=Reservation(part)
    try:q=parity(F,n,B)
    except Refused:q=dict(status='UNKNOWN')
    attempts.append(('parity',q['status'],part,part-B.left))
    if q['status']=='EMPTY':return result(q)
    if witness(q):return result(dict(q,status='WITNESS',route='xor_original_audit'))
    assert root.reserve('modular',part)
    q=modular(F,n,O if O else None,part);attempts.append(('modular',q['status'],part,q['used']))
    if q['status']=='EMPTY':return result(dict(q,route='modular'))
    # Selected chart metric only; never an optimum-width lower bound.
    assert root.reserve('chart',part);B=Reservation(part);chart_score=None
    try:_,chart_score=source_cover(F,n,B)
    except Refused:pass
    attempts.append(('chart','MEASURED' if chart_score is not None else 'UNKNOWN',part,part-B.left))
    share=root.left//2;assert root.reserve('live',share)
    q=live(F,n,A,t,O,share,clip=2);attempts.append(('live',q['status'],share,q['reserved']))
    if q['status']=='WITNESS':assert witness(q);return result(dict(q,route='live'))
    if q['status']=='EMPTY':return result(dict(q,route='live'))
    rest=root.left;assert root.reserve('prior',rest)
    if not O:
        q=prior(F,n,A,t,rest);attempts.append(('prior',q['status'],rest,q.get('reserved',rest)))
        if q['status']=='WITNESS':assert witness(q);return result(q)
        if q['status']=='EMPTY':return result(q)
    else:attempts.append(('prior','NOT_APPLICABLE_EXPLICIT_ONE',rest,0))
    return result(dict(status='UNKNOWN',source=(F,n,A,t,O),selected_chart=chart_score,reason='bounded_portfolio_inconclusive'))


def tseitin(k,odd):
    E=tuple((i,(i+1)%k) for i in range(k))+tuple((i,i+k//2) for i in range(k//2));n=len(E)
    rows=tuple(tuple(j for j,e in enumerate(E) if i in e) for i in range(k));F=tuple(c for i,ids in enumerate(rows) for c in xor_clauses(ids,int(odd and i==0)))
    return F,n


def main():
    from random import Random
    from collections import Counter
    rng=Random(3693302);C=Counter();compare=Counter()
    for k in (8,16,32,64):
        for odd in (False,True):
            F,n=tseitin(k,odd);q=dispatch(F,n,(),(),(),10**7);assert q['status']==('EMPTY' if odd else 'WITNESS');assert q['route'] in ('xor','xor_original_audit');C['tseitin',q['status']]+=1
    for n in (12,20,32,48):
        for planted in (False,True):
            for _ in range(8):
                w=tuple(rng.randrange(2) for i in range(n));F=[]
                for j in range(round(4.26*n)):
                    ids=rng.sample(range(n),3);c=tuple((i+1)*rng.choice((-1,1)) for i in ids)
                    if planted and not accepts((c,),w):c=(-c[0],)+c[1:]
                    F.append(c)
                F=tuple(F);q=dispatch(F,n,(),(),(),200000);status=q['status'];C[n,planted,status]+=1
                old=prior(F,n,(),(),200000);compare[old['status'],status]+=1
                if old['status']=='WITNESS':assert valid(F,n,(),(),(),old['witness'])
                if old['status']!='UNKNOWN' and status!='UNKNOWN':assert old['status']==status
                if status=='WITNESS':assert valid(F,n,(),(),(),q['witness'])
                if status=='UNKNOWN':assert q['source']==(F,n,(),(),()) and q['reserved']==200000
                if planted:assert status!='EMPTY'
                if n==12:
                    W=any(accepts(F,x) for x in product((0,1),repeat=n));assert status=='UNKNOWN' or (status=='WITNESS')==W
    for n in range(1,7):
        for _ in range(16):
            F=tuple(tuple((i+1)*rng.choice((-1,1)) for i in rng.sample(range(n),min(3,n))) for j in range(4));A=(tuple(rng.randrange(3) for i in range(n)),);t=(rng.randrange(3),);O=(tuple(range(n)),)
            W=any(valid(F,n,A,t,O,x) for x in product((0,1),repeat=n));q=dispatch(F,n,A,t,O,1000000)
            assert q['status']==('WITNESS' if W else 'EMPTY');C['mixed']+=1
    assert dispatch(((1,),),1,(),(),(),0)['status']=='UNKNOWN'
    print(dict(C));print('prior versus diagnostic',dict(compare))
if __name__=='__main__':main()
