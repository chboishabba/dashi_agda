"""Restartable original-coordinate oracle for the intrinsic syndrome fold.
Run in batches (timeout 90s per invocation); committed import-path replay.
"""
from itertools import product
from collections import Counter
from random import Random
from pathlib import Path
import argparse,json
from check_p0_signed_contrast_20261125 import canon
from check_pnp_f3_syndrome_boundary import syndrome_fold,conditioned_fold,energy

def case(i):
    rng=Random(3692815+i);n=i%11;R=tuple(j for j in range(n) if rng.randrange(5));r=i%5;t=tuple(rng.randrange(3) for _ in range(r));o=i%3
    I=[R] if i%2 else [R[j:j+3] for j in range(0,len(R),3)]
    F=canon(tuple((j+1)*rng.choice((-1,1)) for j in rng.sample(J,rng.randrange(min(3,len(J))+1))) for J in I for _ in range(i%5))
    cols=tuple(tuple(rng.randrange(3) for _ in range(r+1)) for _ in range(n));H=[0]*3
    for b in product(range(2),repeat=len(R)):
        x=dict(zip(R,b))
        if all(any(x[abs(l)-1]==int(l>0) for l in cl) for cl in F) and tuple(sum(cols[j][a]*x[j] for j in R)%3 for a in range(r))==t:
            H[(o+sum(cols[j][-1]*x[j] for j in R))%3]+=1
    s=Counter(cases=1,points=2**len(R))
    for w in (0,2,6,10):
        for name,fn in (('direct',syndrome_fold),('conditioned',conditioned_fold)):
            q,stats=fn(F,cols,t,o,R,w,4,20000)
            assert stats['work']<=20000
            if q is None:s[name+'_refusals']+=1;continue
            h,m,e=q;z=tuple(a-b for a,b in zip(H,h))
            assert min(z)>=0 and sum(z)<=m and energy(z)<=e*e,(i,w,H,q,stats)
            if m==0:assert tuple(h)==tuple(H)
            s[name+'_accepted']+=1;s[name+'_exact']+=m==0;s[name+'_character_exact']+=e==0;s[name+'_partial']+=m>0
    return s

def dense():
    k=64;n=2*k;F=tuple((2*i+1,2*i+2) for i in range(k));cols=tuple((1,int(i%2==0)) for i in range(n));target=(0,)
    q,st=syndrome_fold(F,cols,target,0,range(n),2,1,1000000)
    A={(0,0):1}
    for i in range(k):
        B={}
        for (s,t),a in A.items():
            for x,y in ((0,1),(1,0),(1,1)):
                p=((s+x+y)%3,(t+x)%3);B[p]=B.get(p,0)+a
        A=B
    h=tuple(A.get((0,d),0) for d in range(3));assert q==(h,0,0)
    assert syndrome_fold(F,cols,target,0,range(n),2,0,1000000)[0] is None
    assert syndrome_fold(F,cols,target,0,range(n),2,1,1)[0] is None
    return dict(hist=h,stats=st)

def main():
    p=argparse.ArgumentParser();p.add_argument('--total',type=int,default=512);p.add_argument('--batch',type=int,default=64);p.add_argument('--checkpoint',type=Path,required=True);a=p.parse_args()
    assert a.batch>0 and a.total>=0
    state=json.loads(a.checkpoint.read_text()) if a.checkpoint.exists() else dict(version=1,total=a.total,next=0,counts={},dense=dense())
    assert state['version']==1 and state['total']==a.total
    c=Counter(state['counts'])
    for i in range(state['next'],min(a.total,state['next']+a.batch)):
        c.update(case(i));state.update(next=i+1,counts=dict(c))
        tmp=a.checkpoint.with_suffix('.tmp');tmp.write_text(json.dumps(state));tmp.replace(a.checkpoint)
    print(json.dumps(state))
if __name__=='__main__':main()
