"""Checkpointed original Boolean oracle and width-growing Fourier controls."""
from check_pnp_dual_syndrome_fourier import *
from random import Random
from collections import Counter
from pathlib import Path
import argparse,json

def case(i):
    rng=Random(3692818+i);n=2+i%9;r=i%5;R=tuple(j for j in range(n) if rng.randrange(5));t=tuple(rng.randrange(3) for _ in range(r));o=i%3
    groups=[R[j:j+3] for j in range(0,len(R),3)]
    F=tuple(tuple((j+1)*rng.choice((-1,1)) for j in rng.sample(G,rng.randrange(1,len(G)+1))) for G in groups for _ in range(i%4))
    cols=tuple(tuple(rng.randrange(3) for _ in range(r+1)) for _ in range(n));w=Q((-1)**i*(1+i%3),3**(i%4));H=[0]*3
    for bits in product(range(2),repeat=len(R)):
        x=dict(zip(R,bits))
        if all(any(x[abs(l)-1]==int(l>0) for l in c) for c in F) and tuple(sum(cols[j][a]*x[j] for j in R)%3 for a in range(r))==t:H[(o+sum(cols[j][-1]*x[j] for j in R))%3]+=1
    v=tuple(w*(3*h-sum(H)) for h in H);s=Counter(fixtures=1,points=2**len(R))
    for cap in (1,3,9,81):
        rec=dual_contrast(F,cols,t,o,R,w,3,cap,100000);s['attempts']+=1
        if rec is None:s['refused']+=1;continue
        a,b,st=rec;assert all(l<=x<=h for l,x,h in zip(a,v,b)),(i,cap,v,rec)
        s['bounds']+=3;s['exact']+=a==b;s['partial']+=a!=b;s['probes']+=st['probes'];s['work']+=st['work']
        if cap==81:assert a==b==v
    return s

def dense(k):
    n=4*k;F=tuple((-(2*i+1),-(2*i+2)) for i in range(2*k));cols=tuple(tuple((1+j%2) if i==(j//2)%k else 0 for i in range(k))+(0,) for j in range(n))
    a,b,st=dual_contrast(F,cols,(0,)*k,0,range(n),Q(1),2,1,100000)
    assert a==b==(2*3**k,-3**k,-3**k) and st['side_ranks']==[k,k] and st['probes']==1
    assert dual_contrast(F,cols,(0,)*k,0,range(n),Q(1),2,1,1) is None
    return st

def chirp(k):
    # Both sides have exactly flat Fourier magnitudes. Opposite phases
    # pointwise cancel, so global correlation is full mass, not zero.
    S=list(product(range(3),repeat=k));q=3**k;energies=[];corr=Z
    for y in S:
        a=b=Z
        for x in S:
            f=sum(t*t for t in x);a=add(a,OMEGA[(f+dot(x,y))%3]);b=add(b,OMEGA[(-f-dot(x,y))%3])
        assert norm(a)==norm(b)==q;corr=add(corr,mul(a,b));energies.append(norm(a))
    assert corr==(q*q,0)
    return dict(rank=k,modes=q,energy_per_mode=q,correlation=q,one_mode_head=1,one_mode_tail=q-1)

def main():
    p=argparse.ArgumentParser();p.add_argument('--total',type=int,default=512);p.add_argument('--batch',type=int,default=64);p.add_argument('--checkpoint',type=Path,required=True);a=p.parse_args();assert a.batch>0 and a.total>=0
    s=json.loads(a.checkpoint.read_text()) if a.checkpoint.exists() else dict(version=1,total=a.total,next=0,counts={})
    assert s['version']==1 and s['total']==a.total;c=Counter(s['counts'])
    for i in range(s['next'],min(a.total,s['next']+a.batch)):
        c.update(case(i));s.update(next=i+1,counts=dict(c));tmp=a.checkpoint.with_suffix('.tmp');tmp.write_text(json.dumps(s));tmp.replace(a.checkpoint)
    if s['next']==a.total:s.update(dense=[dense(k) for k in (1,4,16,64)],chirps=[chirp(k) for k in (1,2,3,4)]);a.checkpoint.write_text(json.dumps(s))
    print(json.dumps(s))
if __name__=='__main__':main()
