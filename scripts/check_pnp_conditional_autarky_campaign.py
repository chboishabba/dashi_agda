from check_pnp_conditional_autarky import *
from random import Random
from collections import Counter
import argparse,json
from pathlib import Path


def case(i):
    r=Random(3692836+i);n=1+i%9
    F=canon(tuple(tuple((j+1)*r.choice((-1,1)) for j in r.sample(range(n),r.randrange(min(n,4)+1))) for _ in range(i%11)))
    D=tuple(r.sample(range(n),1+i%min(n,3)));R=tuple(tuple(r.randrange(3) for _ in range(n)) for _ in range(i%3));t=tuple(r.randrange(3) for _ in R)
    A=list(product((0,1),repeat=n));S=[x for x in A if accepts(F,x)]
    C=Counter(fixtures=1,points=len(A))
    for rows,target in (((),()),(R,t)):
        P,w=project(F,n,D,100000,rows=rows);assert w<=100000
        if P is None:C['refused']+=1;continue
        E=[x for x in S if tuple(sum(a*b for a,b in zip(row,x))%3 for row in rows)==target]
        I=set(D);outside=[j for j in range(n) if j not in I];truth={tuple(x[j] for j in outside):0 for x in A}
        for x in E:truth[tuple(x[j] for j in outside)]+=1
        m=0;image=set()
        for x in A:
            if any(x[j] for j in D):continue
            e=reopen(P,x,target);k=truth[tuple(x[j] for j in outside)]
            assert (e is not None)==bool(k)
            if e is not None:
                y,c=e;assert y in E and c==k;image.add(y);m+=c
            C['fibre_checks']+=1
        assert m==len(E) and len(E)<=len(image)*(1<<len(D));C['completed']+=1
    s,x,G,patches,w=descend(F,n,100000);assert w<=100000 and (s!='EMPTY' or not S) and (x is None or x in S)
    Y=[x for x in A if accepts(G,x)];assert bool(Y)==bool(S)
    for y in Y:assert lift(patches,y) in S
    C[s]+=1;C['patches']+=len(patches);C['reopen']+=len(Y)
    return C


def controls():
    # Equality chain: no single-coordinate unconditional autarky, but all
    # boundary branches have an exact patch; the boundary is retained.
    n=264;F=tuple(c for i in range(1,n) for c in ((-i,i+1),(i,-i-1)))
    s,x,G,P,w=descend(F,n,100000000);assert s=='WITNESS' and accepts(F,x)
    # A conflicting boundary branch becomes one exact blocker.
    Q,wq=project(((1,2),(-1,2)),2,(0,),1000)
    assert Q['G']==((2,),) and reopen(Q,(0,0)) is None and reopen(Q,(0,1))[1]==2
    assert project(F,n,(0,),0)==(None,0)
    return dict(chain=n,patches=len(P),work=w,blocker=True,zero_cap=True)

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--total',type=int,default=512);p.add_argument('--batch',type=int,default=64);p.add_argument('--checkpoint',type=Path,required=True);a=p.parse_args();assert a.batch>0
    s=json.loads(a.checkpoint.read_text()) if a.checkpoint.exists() else dict(total=a.total,next=0,counts={});assert s['total']==a.total;C=Counter(s['counts'])
    for i in range(s['next'],min(a.total,s['next']+a.batch)):
        C.update(case(i));s.update(next=i+1,counts=dict(C));tmp=a.checkpoint.with_suffix('.tmp');tmp.write_text(json.dumps(s));tmp.replace(a.checkpoint)
    if s['next']==a.total:s['controls']=controls();a.checkpoint.write_text(json.dumps(s))
    print(json.dumps(s))
