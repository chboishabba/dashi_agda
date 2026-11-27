"""Replay original small refusal receipts and the 72-column signed square.

Run locally, not CI. Output is a new receipt; do not reuse old fingerprints.
No planted witness supplied to any producer. Trace cost is observational,
separate from charged producer work. All masks serialized losslessly.
"""
from pathlib import Path
from random import Random
from collections import Counter
import json,sys,hashlib,os
from sympy import Matrix
from check_pnp_affine_normal_components import bits,canon,chart,lift,satisfies,Budget
from check_pnp_normal_boundary_join import value
from check_pnp_demand_strata import Allowance,ProbeLimit
from check_pnp_capacity_partition import partition
from check_pnp_signed_capacity_square import row_ledger,pull,pin_pull,bounds,evaluate,screen

HERE=Path(__file__).parent
def valid(R,caps,x):return all((r&x).bit_count()<=c for r,c in zip(R,caps))
def free(n,H):return tuple(1<<j for j in range(n) if j not in {a.bit_length()-1 for a,b in H})
def embedding(n,H,K):
    assert canon(H+K)==K
    f=free(n,H);v,W=chart(n,K)
    return value(f,v),tuple(value(f,w) for w in W)

def small():
    src=json.loads((HERE/'receipts/pnp_capacity_refusal_replay_local_20261127.json').read_text())
    counts=Counter();rows=[];squares=points=compositions=pin_checks=0
    for c in src['cases']:
        n=c['n'];R=tuple(c['rows'])
        for r in c['cases']:
            H=tuple(map(tuple,r['normal_demand']));caps=tuple(r['caps']);u,V=chart(n,H)
            X=[lift(u,V,z) for z in range(1<<len(V))]
            truth=[x for x in X if valid(R,caps,x)];assert len(truth)==r['truth_count']
            B=Budget(1_000_000);Q,y,reason=screen(n,R,H,caps,Allowance(B,B.left))
            assert (y is not None)==bool(truth) and (Q is None)==(not truth)
            if Q is not None:
                assert y in truth and satisfies(y,Q,()) and all(satisfies(x,Q,()) for x in truth)
            counts[reason]+=1
            for i,m in enumerate(row_ledger(row,u,V) for row in R):
                lo,hi=bounds(m)
                for z,x in enumerate(X):
                    w=(R[i]&x).bit_count();assert evaluate(m,z)==2*w and lo<=w<=hi;points+=1
                for a in m:
                    if not a:continue
                    p=a.bit_length()-1
                    for b in (0,1):
                        t,T=chart(len(V),((a,b),));q=pull(m,t,T)
                        folded=pin_pull(m,a,b)
                        assert q=={(k&((1<<p)-1))|((k>>(p+1))<<p):v for k,v in folded.items()}
                        pin_checks+=1
                        orig=lift(0,free(n,H),a);K=canon(H+((orig,b),));v,W=chart(n,K)
                        assert q==row_ledger(R[i],v,W);squares+=1
                        if T:
                            t2,T2=chart(len(T),((1,1),))
                            assert pull(q,t2,T2)==pull(m,lift(t,T,t2),tuple(lift(0,T,z) for z in T2))
                            compositions+=1
            rows.append(dict(source=c['name'],trial=r['trial'],limit=r['limit'],reason=reason,truth=len(truth),dimension=len(V),retained=None if Q is None else n-len(Q),charged=sum(B.stats.values())))
    assert len(rows)==243
    return dict(counts=dict(counts),rows=rows,squares=squares,compositions=compositions,point_checks=points,pin_checks=pin_checks)

def large():
    m,degree,seed=24,9,2;rng=Random(3692700+100*m+10*degree+seed);S=[]
    for _ in range(degree):
        for attempt in range(1000):
            p=list(range(m));rng.shuffle(p);T=[tuple(sorted(p[i:i+3])) for i in range(0,m,3)]
            if not set(T)&set(S):break
        else:raise AssertionError('fixture generation cap')
        S.extend(T)
    rng.shuffle(S);n=len(S);R=tuple(sum(1<<j for j,T in enumerate(S) if i in T) for i in range(m))
    H=canon(tuple((r,1) for r in R));u,V=chart(n,H);M=[row_ledger(r,u,V) for r in R]
    assert n==72 and len(V)==48
    A=Matrix(m,n,lambda i,j:R[i]>>j&1);out={}
    for name,signed in (('baseline',False),('signed',True)):
        trace=[];checks=0
        def record(kind,K,I,reason):
            nonlocal checks
            if K is None:trace.append(dict(kind=kind,empty=True,reason=reason));return
            t,T=embedding(n,H,K);v,W=chart(n,K);N=[row_ledger(r,v,W) for r in R]
            for r,a,b in zip(R,M,N):
                assert pull(a,t,T)==b and evaluate(b,0)==2*(r&v).bit_count();checks+=1
            trace.append(dict(kind=kind,reason=reason,dimension=len(W),demand=[[str(a),b] for a,b in K],remaining=list(I),constant_twice=sum(q.get(0,0) for q in N),modes=sum(sum(a!=0 for a in q) for q in N),amplitude=sum(sum(abs(c) for a,c in q.items() if a) for q in N),all_safe=sum(bounds(q)[1]<=1 for q in N),floor_empty=sum(bounds(q)[0]>1 for q in N),violated=sum((r&v).bit_count()>1 for r in R)))
        B=Budget(20_000_000);z=partition(n,R,H,(1,)*m,Allowance(B,B.left),nodes=256,signed_screen=signed,trace=record)
        assert z.witness is not None and all(x==1 for x in A*Matrix([z.witness>>j&1 for j in range(n)]))
        out[name]=dict(witness=str(z.witness),steps=z.stage,upper=str(z.upper),charged=sum(B.stats.values()),charges=dict(B.stats),square_checks=checks,trace=trace)
    assert out['baseline']['steps']==16 and out['baseline']['charged']==171888
    return out

def main():
    files=sorted(HERE.glob('check_pnp_*.py'))
    key=hashlib.sha256(b''.join(p.name.encode()+b'\0'+p.read_bytes() for p in files)).hexdigest()
    out=dict(key=key,small=small(),large=large())
    path=Path(sys.argv[1]);path.parent.mkdir(parents=True,exist_ok=True)
    tmp=path.with_suffix('.tmp');tmp.write_text(json.dumps(out,indent=2));os.replace(tmp,path)
    print(out['small']['counts'],{k:{a:b for a,b in v.items() if a not in ('trace','charges')} for k,v in out['large'].items()})
if __name__=='__main__':main()
