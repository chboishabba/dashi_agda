"""Checkpointed original-coordinate oracle for the collective F3 normal fold."""
from check_pnp_f3_normal_fold import *
from random import Random
from collections import Counter
from pathlib import Path
import json,argparse

def case(i):
    r=Random(3692816+i);n=i%10;k=i%5;R=tuple(j for j in range(n) if r.randrange(5));cols=tuple(tuple(r.randrange(3) for _ in range(k+1)) for j in range(n));t=tuple(r.randrange(3) for _ in range(k));o=i%3
    F=tuple(tuple((j+1)*r.choice((-1,1)) for j in r.sample(R,r.randrange(min(4,len(R))+1))) for _ in range(i%7))
    if i%4==0:F=tuple((a+1,b+1) for a,b in zip(R,R[1:]))
    H=[0]*3
    for bits in product(range(2),repeat=len(R)):
        x=dict(zip(R,bits))
        if all(any(x[abs(l)-1]==int(l>0) for l in c) for c in F) and tuple(sum(cols[j][a]*x[j] for j in R)%3 for a in range(k))==t:H[(o+sum(cols[j][-1]*x[j] for j in R))%3]+=1
    s=Counter(fixtures=1,points=2**len(R))
    for w in (0,2,3,10):
        h,st=normal_fold(F,cols,t,o,R,6,w,100000);s['attempts']+=1;assert st['work']<=100000
        if h is None:s['refused']+=1;assert w!=10
        else:assert h==tuple(H),(i,h,H,st);s['exact']+=1;s['nonempty']+=bool(sum(h))
    return s

def dense(n):
    F=tuple((i+1,i+2) for i in range(n-1));cols=((1,),)*n
    h,s=normal_fold(F,cols,(),0,range(n),6,2,200000)
    # Independent two-state transfer; adjacent zero pair is forbidden.
    D={(1,0):1}
    for _ in range(n):
        E=Counter()
        for (p,t),v in D.items():
            for b in (0,1):
                if p or b:E[b,(t+b)%3]+=v
        D=E
    H=tuple(sum(D.get((b,d),0) for b in (0,1)) for d in range(3))
    assert H==h,(h,H,s)
    assert normal_fold(F,cols,(),0,range(n),6,0,200000)[0] is None
    assert normal_fold(F,cols,(),0,range(n),6,2,1)[0] is None
    return dict(n=n,h=h,stats=s)

def main():
    p=argparse.ArgumentParser();p.add_argument('--total',type=int,default=512);p.add_argument('--batch',type=int,default=64);p.add_argument('--checkpoint',type=Path,required=True);a=p.parse_args()
    assert a.batch>0 and a.total>=0
    s=json.loads(a.checkpoint.read_text()) if a.checkpoint.exists() else dict(version=1,total=a.total,next=0,counts={})
    assert s['version']==1 and s['total']==a.total
    c=Counter(s['counts'])
    for i in range(s['next'],min(a.total,s['next']+a.batch)):
        c.update(case(i));s.update(next=i+1,counts=dict(c));tmp=a.checkpoint.with_suffix('.tmp');tmp.write_text(json.dumps(s));tmp.replace(a.checkpoint)
    if s['next']==a.total:s['dense']=dense(64);a.checkpoint.write_text(json.dumps(s))
    print(json.dumps(s))
if __name__=='__main__':main()
