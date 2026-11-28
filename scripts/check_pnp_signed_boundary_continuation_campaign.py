"""Reproducible C1a continuation and dense-cut regression.
Run in 16-case batches; all refusal profiles are retained.
"""
from itertools import product
from fractions import Fraction as Q
from random import Random
from collections import Counter
from pathlib import Path
import argparse,json
from check_p0_signed_contrast_20261125 import canon,accepts,value,coefficient,translation,refine,basis
from check_pnp_signed_component_histogram import energy
from check_pnp_signed_boundary_energy import separator

def profile(c):
    if c is None:return None
    F,cols,t,o,R,w,lo,hi=c
    B=basis(cols[i][:-1] for i in R);split=separator(F,cols,t,R,len(R));H=[0]*3
    for bits in product(range(2),repeat=len(R)):
        x=dict(zip(R,bits))
        if all(any(x[abs(l)-1]==int(l>0) for l in cl) for cl in F) and tuple(sum(cols[j][a]*x[j] for j in R)%3 for a in range(len(t)))==t:
            H[(o+sum(cols[j][-1]*x[j] for j in R))%3]+=1
    return dict(free=len(R),rank=len(B),hist=H,energy=energy(H),
                separator=None if split is None else len(split[1]),weight=str(w),
                bounds=[list(map(str,lo)),list(map(str,hi))])

def query(i):
    rng=Random(3692814+i);n=3+i%6;k=1+i%3;L=n+2*k-1;eps=Q(1,8*L)
    F=canon(tuple((j+1)*rng.choice((-1,1)) for j in rng.sample(range(n),rng.randrange(1,min(n,4)+1))) for _ in range(i%13))
    S=[x for x in product(range(2),repeat=n) if accepts(F,x)]
    p=tuple(rng.randrange(3) for _ in range(n+k-1));q=rng.randrange(len(p));e=rng.randrange(k);b=tuple(rng.randrange(3) for _ in range(e))
    s=Counter(fixtures=1);fail=[]
    for typ,roots,vs in [('coefficient',coefficient(F,n,k,p[:q]),[value(S,n,k,p[:q]+(d,)) for d in range(3)]),
                         ('translation',translation(F,n,k,p,b),[value(S,n,k,p,b+(d,)) for d in range(3)])]:
        v=sum(vs)/3;delta=[3*(x-v) for x in vs];s['queries']+=1;s['positive_parents']+=v>Q(1,24)
        for budget in (0,4,32):
            lo,hi,ch,done=refine(roots,eps,budget)
            assert all(a<=x<=z for a,x,z in zip(lo,delta,hi)),(i,typ,lo,delta,hi)
            assert all(delta[d]>=-eps for d in ch)
            s['bound_checks']+=3;s[f'cert_{budget}']+=bool(ch);s[f'splits_{budget}']+=done
        if not ch:
            f=dict(i=i,type=typ,n=n,k=k,F=F,p=p,q=q,e=e,b=b,delta=list(map(str,delta)),roots=[profile(c) for c in roots])
            lo,hi,ch,done=refine(roots,eps,32,exact_probe_budget=16384)
            assert all(a<=x<=z for a,x,z in zip(lo,delta,hi))
            assert all(delta[d]>=-eps for d in ch)
            f['fallback']=dict(choices=ch,lo=list(map(str,lo)),hi=list(map(str,hi)),splits=done,probe_cap=16384)
            fail.append(f);s['fallback_certified']+=bool(ch)
    return s,fail

def main():
    p=argparse.ArgumentParser();p.add_argument('--total',type=int,default=256);p.add_argument('--batch',type=int,default=16);p.add_argument('--checkpoint',type=Path,required=True);a=p.parse_args()
    assert a.batch>0 and a.total>=0
    state=json.loads(a.checkpoint.read_text()) if a.checkpoint.exists() else dict(version=1,total=a.total,next=0,counts={},failures=[])
    assert state['version']==1 and state['total']==a.total
    c=Counter(state['counts'])
    for i in range(state['next'],min(a.total,state['next']+a.batch)):
        s,f=query(i);c.update(s);state['failures'].extend(f);state.update(next=i+1,counts=dict(c))
        tmp=a.checkpoint.with_suffix('.tmp');tmp.write_text(json.dumps(state));tmp.replace(a.checkpoint)
    print(json.dumps(state))
if __name__=='__main__':main()
