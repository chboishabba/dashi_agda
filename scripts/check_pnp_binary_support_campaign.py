from check_pnp_binary_support_endpoint import *
from itertools import product
from random import Random
from collections import Counter
from pathlib import Path
import argparse,json
from check_p0_signed_contrast_20261125 import matrix


def check_case(i):
    rng=Random(3692830+i);n=i%9;r=i%4
    F=canon(tuple(tuple((j+1)*rng.choice((-1,1)) for j in rng.sample(range(n),rng.randrange(min(n,4)+1))) for _ in range(i%11)))
    if i%4==0:F=canon((j+1,(j+1)%n+1) for j in range(n))
    rows=tuple(tuple(rng.randrange(3) for _ in range(n)) for _ in range(r));target=tuple(rng.randrange(3) for _ in range(r))
    if i%3==0:
        x=tuple(rng.randrange(2) for _ in range(n));target=tuple(sum(a*b for a,b in zip(row,x))%3 for row in rows)
    S=[x for x in product(range(2),repeat=n) if accepts(F,x) and tuple(sum(a*b for a,b in zip(row,x))%3 for row in rows)==target]
    C=Counter(fixtures=1,points=2**n,empty=not S,singleton=len(S)==1,multiple=len(S)>1)
    for cap in (0,1048576):
        ledger=ContinuationAllowance(cap);s,x,R=direct(F,n,ledger,rows,target)
        assert s!='EMPTY' or not S
        assert s!='WITNESS' or x in S
        P=()
        for rec in R:
            W=[x for x in S if x[:len(P)]==P];j=rec['i'];actual=tuple(sum(x[j]==d for x in W) for d in (0,1))
            assert rec['parent'][0]<=len(W)<=rec['parent'][1]
            assert all(a<=b<=c for a,b,c in zip(rec['lo'],actual,rec['hi']))
            C['bound_checks']+=3
            if rec['chosen'] is not None:P+=(rec['chosen'],);assert any(x[:len(P)]==P for x in S)
        k=str(cap);C[k+'_'+s]+=1;C[k+'_queries']+=len(R);C[k+'_reserved']+=ledger.total-ledger.left
        if x is not None and n:
            p,b=identity_isolation(x);A=matrix(n,n,p);assert [y for y in S if tuple(sum(a*z for a,z in zip(row,y))%3 for row in A)==b]==[x];C['isolation']+=1
        ledger=ContinuationAllowance(cap);s,W,_=classify(F,n,ledger,rows=rows,target=target)
        assert all(x in S for x in W) and len(set(W))==len(W)
        assert s!='EMPTY' or not S
        assert s!='SINGLETON' or len(S)==1
        assert s!='MULTIPLE' or len(S)>=2
        C[k+'_class_'+s]+=1
        assert ledger.left+sum(ledger.charges.values())==cap
    if i<64:
        G=guarded(F,n);S0=[x for x in product(range(2),repeat=n) if accepts(F,x)]
        H=[x for x in product(range(2),repeat=n+1) if accepts(G,x)]
        assert set(H)=={(0,)*(n+1)}|{x+(1,) for x in S0}
        ledger=ContinuationAllowance(1048576);s,W,_=classify(G,n+1,ledger,known=(0,)*(n+1))
        assert s in ('SINGLETON','MULTIPLE','UNKNOWN') and (s!='SINGLETON' or not S0) and (s!='MULTIPLE' or S0)
        C['guarded_'+s]+=1
    return C


def controls():
    # All equal-size two-child mass enclosures including a negative
    # contrast for an inhabited child, and inherited mass progress.
    checks=0
    for a,b in product(range(12),repeat=2):
        m=a+b;d=(3*a-m,3*b-m,-m)
        for e in (0,1,3,7):
            lo=tuple(x-e for x in d);hi=tuple(x+e for x in d)
            L,U,l,u=child_bounds(lo,hi,m,m)
            assert L[0]<=a<=U[0] and L[1]<=b<=U[1] and l==u==m;checks+=1
    F=((-8,-6,7),(-8,-5,1,4),(-5,-4,1,3),(-4,-1,5,7),(-1,4,6),(2,5,6));out=[]
    for cap in (0,1048576):
        ledger=ContinuationAllowance(cap);s,x,R=direct(F,8,ledger);assert s=='WITNESS' and accepts(F,x)
        out.append(dict(cap=cap,witness=x,queries=len(R),splits=sum(q['splits'] for q in R),reserved=cap-ledger.left))
    return dict(interval_checks=checks,hard=out)

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--total',type=int,default=256);p.add_argument('--batch',type=int,default=32);p.add_argument('--checkpoint',type=Path,required=True);a=p.parse_args();assert a.batch>0 and a.total>=0
    s=json.loads(a.checkpoint.read_text()) if a.checkpoint.exists() else dict(total=a.total,next=0,counts={});assert s['total']==a.total;C=Counter(s['counts'])
    for i in range(s['next'],min(a.total,s['next']+a.batch)):
        C.update(check_case(i));s.update(next=i+1,counts=dict(C));tmp=a.checkpoint.with_suffix('.tmp');tmp.write_text(json.dumps(s));tmp.replace(a.checkpoint)
    if s['next']==a.total:s['controls']=controls();a.checkpoint.write_text(json.dumps(s))
    print(json.dumps(s))
