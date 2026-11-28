"""Same original continuation oracle, shared capped-producer reservations."""
from check_p0_signed_contrast_20261125 import canon,accepts,value,coefficient,translation,refine,ContinuationAllowance
from random import Random
from itertools import product
from fractions import Fraction as Q
from collections import Counter
from pathlib import Path
import argparse,json

def case(i):
    rng=Random(3692814+i);n=3+i%6;k=1+i%3;L=n+2*k-1;eps=Q(1,8*L)
    F=canon(tuple((j+1)*rng.choice((-1,1)) for j in rng.sample(range(n),rng.randrange(1,min(n,4)+1))) for _ in range(i%13))
    S=[x for x in product(range(2),repeat=n) if accepts(F,x)];p=tuple(rng.randrange(3) for _ in range(n+k-1));q=rng.randrange(len(p));e=rng.randrange(k);b=tuple(rng.randrange(3) for _ in range(e));s=Counter(fixtures=1)
    for typ,args,vs in [('coefficient',(F,n,k,p[:q]),[value(S,n,k,p[:q]+(d,)) for d in range(3)]),('translation',(F,n,k,p,b),[value(S,n,k,p,b+(d,)) for d in range(3)])]:
        v=sum(vs)/3;delta=[3*(x-v) for x in vs]
        for cap in (0,65536,262144,1048576):
            ledger=ContinuationAllowance(cap);roots=(coefficient if typ=='coefficient' else translation)(*args,ledger=ledger)
            lo,hi,ch,done=refine(roots,eps,4,ledger=ledger)
            assert all(a<=x<=z for a,x,z in zip(lo,delta,hi)) and all(delta[d]>=-eps for d in ch),(i,typ,cap,delta,lo,hi)
            assert ledger.left>=0 and sum(ledger.charges.values())+ledger.left==cap
            key=str(cap);s[key+'_queries']+=1;s[key+'_certified']+=bool(ch);s[key+'_splits']+=done;s[key+'_reserved']+=cap-ledger.left;s[key+'_baseline_cells']+=ledger.baseline_cells;s[key+'_boundary_attempts']+=ledger.boundary_attempts;s['bounds']+=3
    return s

def main():
    p=argparse.ArgumentParser();p.add_argument('--total',type=int,default=256);p.add_argument('--batch',type=int,default=16);p.add_argument('--checkpoint',type=Path,required=True);a=p.parse_args();assert a.batch>0 and a.total>=0
    s=json.loads(a.checkpoint.read_text()) if a.checkpoint.exists() else dict(version=1,total=a.total,next=0,counts={});assert s['version']==1 and s['total']==a.total;c=Counter(s['counts'])
    for i in range(s['next'],min(a.total,s['next']+a.batch)):
        c.update(case(i));s.update(next=i+1,counts=dict(c));tmp=a.checkpoint.with_suffix('.tmp');tmp.write_text(json.dumps(s));tmp.replace(a.checkpoint)
    print(json.dumps(s))
if __name__=='__main__':main()
