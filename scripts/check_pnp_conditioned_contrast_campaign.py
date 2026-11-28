"""Restartable independent oracle for the actual conditioned contrast producer.
Run: python scripts/check_pnp_conditioned_contrast_campaign.py --batch 64
Reinvoke until next == total. No solver claims beyond the checked finite cases.
"""
from argparse import ArgumentParser
from fractions import Fraction as Q
from itertools import product
from random import Random
from pathlib import Path
import json
from check_p0_signed_contrast_20261125 import canon, cell, accepts

def case(i):
    rng=Random(2026112806+i); n=1+i%9; r=i%5
    F=canon(tuple((j+1)*rng.choice((-1,1)) for j in rng.sample(range(n),rng.randrange(1,min(n,4)+1))) for _ in range(i%11))
    cols=tuple(tuple(rng.randrange(3) for _ in range(r+1)) for j in range(n))
    target=tuple(rng.randrange(3) for _ in range(r)); o=rng.randrange(3)
    w=Q(rng.choice((-2,-1,1,2)),3**(i%6))
    H=[0]*3
    for x in product(range(2),repeat=n):
        if accepts(F,x) and tuple(sum(cols[j][a]*x[j] for j in range(n))%3 for a in range(r))==target:
            H[(o+sum(cols[j][-1]*x[j] for j in range(n)))%3]+=1
    v=tuple(w*(3*h-sum(H)) for h in H)
    def bounds(conditioned):
        c=cell(F,cols,target,o,tuple(range(n)),w,conditioned=conditioned)
        return c[-2:] if c is not None else ((0,)*3,(0,)*3)
    old,new=bounds(False),bounds(True)
    assert sum(v)==0
    assert all(old[0][d]<=new[0][d]<=v[d]<=new[1][d]<=old[1][d] for d in range(3)), (i,F,cols,target,o,w,v,old,new)
    return int(old!=new),int(v==new[0]==new[1])

def main():
    p=ArgumentParser()
    p.add_argument("--batch",type=int,default=64)
    p.add_argument("--total",type=int,default=2048)
    p.add_argument("--checkpoint",type=Path,default=Path("conditioned_contrast_checkpoint.json"))
    a=p.parse_args()
    assert a.batch>0 and a.total>=0
    state=json.loads(a.checkpoint.read_text()) if a.checkpoint.exists() else dict(version=1,next=0,total=a.total,bounds=0,strict_tightened=0,exact=0)
    assert state["version"]==1 and state["total"]==a.total
    for i in range(state["next"],min(a.total,state["next"]+a.batch)):
        tight,exact=case(i)
        state["next"]=i+1;state["bounds"]+=3;state["strict_tightened"]+=tight;state["exact"]+=exact
        tmp=a.checkpoint.with_suffix(".tmp");tmp.write_text(json.dumps(state,sort_keys=True));tmp.replace(a.checkpoint)
    print(json.dumps(state,sort_keys=True))
if __name__=="__main__":main()
