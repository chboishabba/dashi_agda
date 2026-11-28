"""Checkpointed signed intersection and low-rank cube-character oracle."""
from itertools import product
from fractions import Fraction as Q
from random import Random
from pathlib import Path
from collections import Counter
import argparse,json
from check_pnp_mobius_character import mobius_contrast
from check_pnp_dual_syndrome_fourier import ONE,Z,OMEGA,add,mul,phase,contrast


def case(i):
    rng=Random(3692822+i);n=i%11;r=i%5;R=tuple(j for j in range(n) if rng.randrange(5));t=tuple(rng.randrange(3) for _ in range(r));o=i%3;w=Q((-1)**i*(1+i%3),3**(i%4))
    F=tuple(tuple((j+1)*rng.choice((-1,1)) for j in rng.sample(R,rng.randrange(min(4,len(R))+1))) for _ in range(i%13))
    if i%7==0:F=tuple((a+1,b+1) for a,b in zip(R,R[1:]))
    cols=tuple(tuple(rng.randrange(3) for _ in range(r+1)) for j in range(n));H=[0]*3
    for b in product(range(2),repeat=len(R)):
        x=dict(zip(R,b))
        if all(any(x[abs(l)-1]==int(l>0) for l in c) for c in F) and tuple(sum(cols[j][a]*x[j] for j in R)%3 for a in range(r))==t:H[(o+sum(cols[j][-1]*x[j] for j in R))%3]+=1
    s=Counter(fixtures=1,points=2**len(R));v=tuple(w*(3*h-sum(H)) for h in H)
    for cap in (1,16,128,4096):
        q=mobius_contrast(F,cols,t,o,R,w,4,cap,1000000);s['attempts']+=1
        if q is None:s['refused']+=1;assert cap!=4096
        else:
            a,b,st=q;assert a==b==v,(i,cap,q,v);s['exact']+=1;s['work']+=st['work'];s['terms']+=st['terms'];s['cube_states']+=st['cube_states']
    return s


def selector(k):
    # Every selector pattern triggers a different required data bit.
    # Falsifying cubes are pairwise disjoint, but the CNF is connected.
    m=2**k;n=k+m
    F=tuple(tuple((j+1)*(1 if not (i>>j&1) else -1) for j in range(k))+(k+i+1,) for i in range(m))
    cols=((0,),)*k+((1,),)*m
    q=mobius_contrast(F,cols,(),0,range(n),Q(1),0,m+1,10000000)
    z=(m,0)
    for _ in range(m-1):z=mul(z,add(ONE,OMEGA[1]))
    z=phase(z,1);a,b,st=q;assert a==b==contrast(z) and st['terms']==m+1
    assert mobius_contrast(F,cols,(),0,range(n),Q(1),0,1,10000000) is None
    return dict(selector_bits=k,variables=n,clauses=m,character=z,stats=st,model_count=str(m*2**(m-1)))


def main():
    p=argparse.ArgumentParser();p.add_argument('--total',type=int,default=512);p.add_argument('--batch',type=int,default=64);p.add_argument('--checkpoint',type=Path,required=True);a=p.parse_args();assert a.batch>0 and a.total>=0
    s=json.loads(a.checkpoint.read_text()) if a.checkpoint.exists() else dict(version=1,total=a.total,next=0,counts={});assert s['version']==1 and s['total']==a.total;c=Counter(s['counts'])
    for i in range(s['next'],min(a.total,s['next']+a.batch)):
        c.update(case(i));s.update(next=i+1,counts=dict(c));tmp=a.checkpoint.with_suffix('.tmp');tmp.write_text(json.dumps(s));tmp.replace(a.checkpoint)
    if s['next']==a.total:
        s['selector']=[selector(k) for k in (2,4,6,8)]
        assert mobius_contrast((),((1,0),),(0,),0,(0,),Q(1),0,1,10000) is None
        assert mobius_contrast((),((1,0),),(0,),0,(0,),Q(1),1,1,0) is None
        a.checkpoint.write_text(json.dumps(s))
    print(json.dumps(s))
if __name__=='__main__':main()
