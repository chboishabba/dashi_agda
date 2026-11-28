from check_pnp_constructive_descent import search
from check_p0_signed_contrast_20261125 import canon,accepts,value
from fractions import Fraction as Q
from itertools import product
from random import Random
from collections import Counter
from pathlib import Path
import argparse,json

def case(i):
    r=Random(3692829+i);n=1+i%6
    F=canon(tuple((j+1)*r.choice((-1,1)) for j in r.sample(range(n),r.randrange(1,min(n,3)+1))) for _ in range(i%12))
    S=[x for x in product(range(2),repeat=n) if accepts(F,x)]
    C=Counter(fixtures=1,sat=bool(S),unsat=not S,points=2**n)
    for cap in (0,1048576):
        x,rec=search(F,n,cap,4,0);assert x is None or x in S
        C[str(cap)+'_witness']+=x is not None;C[str(cap)+'_unknown']+=x is None
        C[str(cap)+'_attempts']+=len(rec);C[str(cap)+'_reserved']+=sum(a['reserved'] for a in rec)
        for a in rec:
            k=a['k'];P=();B=();L=n+2*k-1;V=value(S,n,k,P,B)
            for s in a['steps'][:L]:
                d=s['direction'];C['certificate_queries']+=1
                if d is None:break
                if len(P)<n+k-1:P+=(d,)
                else:B+=(d,)
                U=value(S,n,k,P,B);assert 3*(U-V)>=-Q(1,8*L);V=U;C['descent_checks']+=1
            if len(P)==n+k-1 and len(B)==k and V>0:assert V==1;C['positive_terminal']+=1
        if cap==1048576 and S:assert x is not None,(i,F,rec)
    if S:
        good=[k for k in range(1,n+2) if 2*len(S)<=3**k<6*len(S)]
        assert good and all(value(S,n,k,())>Q(1,12) for k in good);C['root_promises']+=1
    return C

def prior_hard_control():
    F=[[-8,-6,7],[-8,-5,1,4],[-5,-4,1,3],[-4,-1,5,7],[-1,4,6],[2,5,6]]
    out=[]
    for cap in (0,1048576):
        x,rec=search(F,8,cap,4,0)
        assert x is not None and accepts(F,x) and all(a['reserved']<=cap for a in rec)
        out.append(dict(cap=cap,witness=x,attempts=[dict(k=a['k'],status=a['status'],reserved=a['reserved']) for a in rec]))
    assert any(a['reserved'] for a in out[1]['attempts'])
    return out

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--total',type=int,default=128);p.add_argument('--batch',type=int,default=16);p.add_argument('--checkpoint',type=Path,required=True);a=p.parse_args();assert a.batch>0 and a.total>=0
    s=json.loads(a.checkpoint.read_text()) if a.checkpoint.exists() else dict(total=a.total,next=0,counts={});assert s['total']==a.total;C=Counter(s['counts'])
    for i in range(s['next'],min(a.total,s['next']+a.batch)):
        C.update(case(i));s.update(next=i+1,counts=dict(C));tmp=a.checkpoint.with_suffix('.tmp');tmp.write_text(json.dumps(s));tmp.replace(a.checkpoint)
    if s['next']==a.total:s['hard_control']=prior_hard_control();a.checkpoint.write_text(json.dumps(s))
    print(json.dumps(s))
