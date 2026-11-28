from check_pnp_stack_fractran import *
from random import Random
from collections import Counter
from sympy import prime
import argparse,json
from pathlib import Path

def case(i):
    r=Random(3692827+i);q=1+i%3;a=1+i%3;blank=i%a
    rules=tuple((r.randrange(q),r.randrange(a),r.randrange(q),r.randrange(a),r.choice((-1,0,1))) for _ in range(i%8))
    M=compile_stack(q,a,blank,rules);run=Runner(M);C=Counter(tables=1)
    one=lambda n,j:tuple(int(k==j) for k in range(n))
    bits=one(a,blank)+one(q,0)+one(q,q-1)+tuple(v for x,y,z,w,d in rules for v in one(q,x)+one(a,y)+one(q,z)+one(a,w)+one(3,d+1))
    N,ini,acc=compile_candidate_bits(q,a,len(rules),bits);assert (N.sparse,N.tags,ini,acc)==(M.sparse,M.tags,0,q-1);C['static_bits']+=1
    for j in range(4):
        c=(r.randrange(q),tuple(r.randrange(a) for _ in range(j%3)),tuple(r.randrange(a) for _ in range(1+j%3)))
        v=M.encode(*c);assert M.decode(v)==(*c,False);z=source_next(M,c)
        u,h,S=run.step(v);w,k,T=run.step(v,False,100000);assert (u,h,S['raw'])==(w,k,T['raw']);assert M.decode(u)==(*(z if z is not None else c),z is None)
        C['one_step']+=1;C['halt']+=h;C['raw']+=S['raw'];C['literal']+=S['literal'];C['jumps']+=S['jumps'];C['guard_checks']+=S['checks']
    c=(0,(blank,), (blank,blank));v=M.encode(*c)
    for _ in range(4):
        z=source_next(M,c);v,h,S=run.step(v);assert M.decode(v)==(*(z if z is not None else c),z is None);C['multi_step']+=1
        if h:break
        c=z
    if i<16:
        P=tuple(int(prime(k+1)) for k in range(len(M.tags)));prog=M.fractions(P);c=(0,(),(blank,));v=M.encode(*c);u,h,S=run.step(v);x=prod(p**e for p,e in zip(P,v))
        for _ in range(S['raw']):
            f=next((f for f in prog if x%f.denominator==0),None);assert f is not None;x=x//f.denominator*f.numerator
        assert x==prod(p**e for p,e in zip(P,u));C['integer']+=1
    return C

def huge():
    M=compile_stack(1,3,0,((0,1,0,2,-1),));run=Runner(M);N=128;c=(0,(2,)*N,(1,)*N);v=M.encode(*c);u,h,S=run.step(v);assert not h and M.decode(u)==(*source_next(M,c),False);assert S['raw']>10**50 and S['literal']<20
    return dict(word_length=N,program_fractions=len(M.sparse),lanes=len(M.tags),**S)

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--total',type=int,default=256);p.add_argument('--batch',type=int,default=32);p.add_argument('--checkpoint',type=Path,required=True);a=p.parse_args();assert a.batch>0 and a.total>=0
    s=json.loads(a.checkpoint.read_text()) if a.checkpoint.exists() else dict(total=a.total,next=0,counts={});assert s['total']==a.total;C=Counter(s['counts'])
    for i in range(s['next'],min(a.total,s['next']+a.batch)):
        C.update(case(i));s.update(next=i+1,counts=dict(C));tmp=a.checkpoint.with_suffix('.tmp');tmp.write_text(json.dumps(s));tmp.replace(a.checkpoint)
    if s['next']==a.total:s['huge']=huge();a.checkpoint.write_text(json.dumps(s))
    print(json.dumps(s))
