"""Independent original-coordinate oracle; resumable finite checks."""
from itertools import product
from random import Random
from pathlib import Path
from argparse import ArgumentParser
import json
from check_pnp_signed_component_histogram import component_bounds,convolve

def case(i):
    rng=Random(3692807+i); n=i%11; R=tuple(j for j in range(n) if rng.randrange(4)); r=i%6
    F=tuple(tuple((j+1)*rng.choice((-1,1)) for j in rng.sample(R,rng.randrange(min(4,len(R))+1))) for _ in range(i%7))
    cols=tuple(tuple(rng.randrange(3) for _ in range(r+1)) for _ in range(n)); t=tuple(rng.randrange(3) for _ in range(r)); o=i%3
    H=[0]*3
    for b in product(range(2),repeat=len(R)):
        x=dict(zip(R,b))
        if all(any(x[abs(l)-1]==int(l>0) for l in c) for c in F) and tuple(sum(cols[j][a]*x[j] for j in R)%3 for a in range(r))==t:
            H[(o+sum(cols[j][-1]*x[j] for j in R))%3]+=1
    for w in (0,2,6,10):
        exact,C,h=component_bounds(F,cols,t,o,R,w)
        assert sum(H)<=C and all(a<=b for a,b in zip(H,h)),(i,w,H,C,h)
        if exact:assert tuple(H)==h and sum(H)==C
        if w==10:assert exact
    return dict(cases=1,points=2**len(R),bounds=12)

def dense():
    for k in (4,16,32,64,128):
        # Each pair obeys x+y=1 (exactly two local Boolean points), with
        # observable x. Dense invertible row mixing hides the independent pairs.
        n=2*k; rows=[[int(j//2==i) for j in range(n)] for i in range(k)]
        for i in range(k-1):rows[i]=[(a+b)%3 for a,b in zip(rows[i],rows[i+1])]
        t=(2,)*(k-1)+(1,); cols=tuple(tuple(row[j] for row in rows)+(int(j%2==0),) for j in range(n))
        exact,C,H=component_bounds((),cols,t,0,range(n),1)
        expected=(1,0,0)
        for _ in range(k):expected=convolve(expected,(1,1,0))
        assert exact and C==2**k and H==expected
    # Wide nonlinear component: zero width refuses, still bounds correctly.
    n=18; F=tuple((i+1,i+2) for i in range(n-1)); cols=((1,),)*n
    done,C,H=component_bounds(F,cols,(),0,range(n),0);assert not done and C>0 and sum(H)>0

def main():
    p=ArgumentParser();p.add_argument('--total',type=int,default=2048);p.add_argument('--batch',type=int,default=128);p.add_argument('--checkpoint',type=Path,default=Path('histogram_checkpoint.json'));a=p.parse_args()
    assert a.batch>0 and a.total>=0
    s=json.loads(a.checkpoint.read_text()) if a.checkpoint.exists() else dict(version=1,total=a.total,next=0,counts={})
    assert s['total']==a.total and s['version']==1
    dense()
    for i in range(s['next'],min(a.total,s['next']+a.batch)):
        for k,v in case(i).items():s['counts'][k]=s['counts'].get(k,0)+v
        s['next']=i+1;tmp=a.checkpoint.with_suffix('.tmp');tmp.write_text(json.dumps(s));tmp.replace(a.checkpoint)
    print(json.dumps(s))
if __name__=='__main__':main()
