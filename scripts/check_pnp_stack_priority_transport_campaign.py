from check_pnp_stack_priority_transport import *
from random import Random
from collections import Counter
from itertools import product
import argparse,json
from pathlib import Path


def case(i):
    r=Random(3692838+i);q=1+i%3;a=1+i%3;blank=i%a
    rules=tuple((r.randrange(q),r.randrange(a),r.randrange(q),r.randrange(a),r.choice((-1,0,1))) for _ in range(i%9))
    M=compile_stack(q,a,blank,rules);run=AuditedRunner(M);C=Counter(fixtures=1,edges=len(M.sparse),loop_phases=len(M.loops))
    for _ in range(4):
        c=(r.randrange(q),tuple(r.randrange(a) for _ in range(r.randrange(4))),tuple(r.randrange(a) for _ in range(1+r.randrange(4))))
        v=M.encode(*c);u,h,S=run.exact(v);w,k,T=run.exact(v,False)
        assert (u,h,S['raw'])==(w,k,T['raw'])
        x=source_next(M,c);assert h==(x is None) and M.decode(u)[:3]==(c if x is None else x)
        C.update(S);C['endpoints']+=1;C['halts']+=h
    return C


def controls():
    M=compile_stack(1,3,0,((0,1,0,2,-1),));run=AuditedRunner(M)
    v=M.encode(0,(2,)*128,(1,)*128);u,h,S=run.exact(v)
    assert not h and M.decode(u)[:3]==source_next(M,(0,(2,)*128,(1,)*128))
    return dict(S,lanes=len(M.tags),fractions=len(M.sparse))

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--total',type=int,default=256);p.add_argument('--batch',type=int,default=32);p.add_argument('--checkpoint',type=Path,required=True);a=p.parse_args();assert a.batch>0
    s=json.loads(a.checkpoint.read_text()) if a.checkpoint.exists() else dict(total=a.total,next=0,counts={});assert s['total']==a.total;C=Counter(s['counts'])
    for i in range(s['next'],min(a.total,s['next']+a.batch)):
        C.update(case(i));s.update(next=i+1,counts=dict(C));tmp=a.checkpoint.with_suffix('.tmp');tmp.write_text(json.dumps(s));tmp.replace(a.checkpoint)
    if s['next']==a.total:s['controls']=controls();a.checkpoint.write_text(json.dumps(s))
    print(json.dumps(s))
