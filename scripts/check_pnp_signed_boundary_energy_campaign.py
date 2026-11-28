"""P vs NP absolute spectral and priority-block replay; checkpoint by case.
Exact original-coordinate oracle. No universal affordability claim.
"""
from itertools import product
from fractions import Fraction as Q
from random import Random
from collections import Counter
from pathlib import Path
import argparse,json
from check_p0_signed_contrast_20261125 import canon
from check_pnp_signed_component_histogram import component_bounds,energy,convolve
from check_pnp_signed_boundary_energy import boundary_contrast
from check_pnp_fractran_guarded_block import compile_block,jump

def spectral_case(i):
    rng=Random(3692812+i);n=4+i%9;R=tuple(range(n));r=i%4
    F=canon(tuple((j+1)*rng.choice((-1,1)) for j in rng.sample(R,rng.randrange(1,min(4,n)+1))) for _ in range(i%12))
    if i%3==0:F=canon(F+tuple((j+1,j+2) for j in range(n-1)))
    cols=tuple(tuple(rng.randrange(3) for _ in range(r+1)) for _ in R)
    t=tuple(rng.randrange(3) for _ in range(r));o=i%3;w=Q(rng.choice((-2,-1,1,2)),3**(i%5));H=[0]*3
    for x in product(range(2),repeat=n):
        if all(any(x[abs(l)-1]==int(l>0) for l in c) for c in F) and tuple(sum(cols[j][a]*x[j] for j in R)%3 for a in range(r))==t:
            H[(o+sum(cols[j][-1]*x[j] for j in R))%3]+=1
    v=tuple(w*(3*h-sum(H)) for h in H);s=Counter(cases=1,points=2**n)
    for width in (0,2,6,12):
        done,C,h,E=component_bounds(F,cols,t,o,R,width,spectral=True)
        assert E>=energy(H) and C>=sum(H) and all(a<=b for a,b in zip(H,h));s['energy_checks']+=1
        if done:assert tuple(H)==h and C==sum(H) and E==energy(H)
        if not done and E==0:s['unresolved_zero_character']+=1
        a=boundary_contrast(F,cols,t,o,R,w,width,3)
        if a is None:s['separator_refusal']+=1;continue
        lo,hi,rec=a;assert all(l<=x<=h for l,x,h in zip(lo,v,hi)),(i,width,v,lo,hi,rec)
        s['separator_checks']+=1;s['omitted_fibres']+=rec['omitted'];s['retained_fibres']+=rec['retained'];s['exact_separator']+=int(lo==hi)
    return s

def literal(v,rules,chosen,k):
    for i in chosen*k:
        j=next((j for j,(g,d) in enumerate(rules) if all(a>=b for a,b in zip(v,g))),None)
        if i!=j:return None
        v=tuple(a+b for a,b in zip(v,rules[i][1]))
    return v

def block_case(i):
    rng=Random(3692813+i);n=rng.randrange(1,5);rules=[]
    for j in range(rng.randrange(1,7)):
        g=tuple(rng.randrange(6) for _ in range(n));d=tuple(rng.randrange(-a,5) for a in g);rules.append((g,d))
    chosen=tuple(rng.randrange(len(rules)) for _ in range(rng.randrange(1,5)));v=tuple(rng.randrange(15) for _ in range(n));k=rng.randrange(10)
    ans=jump(v,compile_block(rules,chosen),k)
    assert ans==literal(v,rules,chosen,k),(i,rules,chosen,v,k,ans)
    return dict(blocks=1,legal_blocks=int(ans is not None))

def main():
    p=argparse.ArgumentParser();p.add_argument('--mode',choices=('spectral','block'),required=True);p.add_argument('--total',type=int,required=True);p.add_argument('--batch',type=int,default=128);p.add_argument('--checkpoint',type=Path,required=True);a=p.parse_args()
    assert a.total>=0 and a.batch>0
    state=json.loads(a.checkpoint.read_text()) if a.checkpoint.exists() else dict(version=1,mode=a.mode,total=a.total,next=0,counts={})
    assert (state['version'],state['mode'],state['total'])==(1,a.mode,a.total)
    counts=Counter(state['counts']);f=spectral_case if a.mode=='spectral' else block_case
    for i in range(state['next'],min(a.total,state['next']+a.batch)):
        counts.update(f(i));state.update(next=i+1,counts=dict(counts))
        tmp=a.checkpoint.with_suffix('.tmp');tmp.write_text(json.dumps(state));tmp.replace(a.checkpoint)
    print(json.dumps(state))
if __name__=='__main__':main()
