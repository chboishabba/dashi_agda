"""Checkpointed original Boolean oracle for transactional prefix bounds."""
from itertools import product
from random import Random
from fractions import Fraction as Q
from collections import Counter
from pathlib import Path
import argparse,json
from check_pnp_mobius_prefix import prefix_contrast

def case(i):
    rng=Random(3692823+i);n=1+i%10;r=i%7;R=tuple(j for j in range(n) if rng.randrange(5));t=tuple(rng.randrange(3) for _ in range(r));o=i%3;w=Q((-1)**i*(1+i%3),3**(i%4))
    F=tuple(tuple((j+1)*rng.choice((-1,1)) for j in rng.sample(R,rng.randrange(min(4,len(R))+1))) for _ in range(i%13))
    if i%4==0:F=tuple((a+1,b+1) for a,b in zip(R,R[1:]))
    cols=tuple(tuple(rng.randrange(3) for _ in range(r+1)) for j in range(n));H=[0]*3
    for b in product(range(2),repeat=len(R)):
        x=dict(zip(R,b))
        if all(any(x[abs(l)-1]==int(l>0) for l in c) for c in F) and tuple(sum(cols[j][a]*x[j] for j in R)%3 for a in range(r))==t:H[(o+sum(cols[j][-1]*x[j] for j in R))%3]+=1
    s=Counter(fixtures=1,points=2**len(R));v=tuple(w*(3*h-sum(H)) for h in H)
    for terms,work in ((1,32),(2,128),(8,512),(4096,100000)):
        q=prefix_contrast(F,cols,t,o,R,w,terms,work);s['attempts']+=1
        if q is None:s['refused']+=1;assert work!=100000;continue
        a,b,st=q;assert st['work']<=work and all(l<=x<=u for l,x,u in zip(a,v,b)),(i,terms,work,v,q)
        assert all(0<=p-h<=c for p,h,c in zip(st['head'],H,st['removed_label_caps']))
        s['exact']+=a==b;s['partial']+=a!=b;s['checks']+=3;s['work']+=st['work'];s['chart_points']+=st['chart_points']
        if work==100000:assert a==b==v
    return s

def controls():
    # Whole cube on x+y+z=1 has zero character, but its subset x=1
    # has nonzero character. A magnitude bound on subsets is invalid.
    pts=[x for x in product(range(2),repeat=3) if sum(x)%3==1]
    assert sorted((x[1]+2*x[2])%3 for x in pts)==[0,1,2]
    assert [x for x in pts if x[0]]==[(1,0,0)]
    # High rank, low nullity: actual original Boolean chart, not F3 volume.
    n=64;cols=tuple(tuple(int(i==j) for i in range(n))+(1,) for j in range(n))
    q=prefix_contrast((),cols,(1,)*n,0,range(n),Q(1),1,1024)
    assert q[0]==q[1]==(-1,2,-1) and q[2]['chart_points']==1
    # Many independent false cubes: truncated prefix remains sound and
    # certifies a nonzero direction without expanding the intersection lattice.
    n=40;F=tuple((1,)+tuple(range(j,j+8)) for j in range(2,33));cols=((1,),)+((0,),)*(n-1)
    q=prefix_contrast(F,cols,(),0,range(n),Q(1),2,100000)
    assert q is not None and not q[2]['exact'] and q[0][1]>0
    return dict(high_rank=q is not None,partial_head=q[2]['head'],partial_caps=q[2]['removed_label_caps'],partial_lo=list(map(str,q[0])),partial_hi=list(map(str,q[1])),partial_prefix=q[2]['prefix'])

def main():
    p=argparse.ArgumentParser();p.add_argument('--total',type=int,default=512);p.add_argument('--batch',type=int,default=64);p.add_argument('--checkpoint',type=Path,required=True);a=p.parse_args();assert a.batch>0 and a.total>=0
    s=json.loads(a.checkpoint.read_text()) if a.checkpoint.exists() else dict(version=1,total=a.total,next=0,counts={});assert s['version']==1 and s['total']==a.total;c=Counter(s['counts'])
    for i in range(s['next'],min(a.total,s['next']+a.batch)):
        c.update(case(i));s.update(next=i+1,counts=dict(c));tmp=a.checkpoint.with_suffix('.tmp');tmp.write_text(json.dumps(s));tmp.replace(a.checkpoint)
    if s['next']==a.total:s['controls']=controls();a.checkpoint.write_text(json.dumps(s))
    print(json.dumps(s))
if __name__=='__main__':main()
