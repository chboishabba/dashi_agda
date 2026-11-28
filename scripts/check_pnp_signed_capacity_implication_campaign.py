"""Cross-plane affine implication acceptance; local truth oracles only.
Run directly with a fresh output path. No CI. Native kernels separate.
"""
from itertools import combinations
from collections import Counter
from random import Random
from pathlib import Path
from sympy import Matrix
import hashlib,json,sys,os
from check_pnp_affine_normal_components import canon,chart,lift,satisfies,Budget
from check_pnp_signed_capacity_square import add,evaluate
from check_pnp_signed_capacity_rank2 import portfolio,observe
from check_pnp_signed_capacity_implication import deduce,propagate,verify_receipts,screen


def original(d,rows):
    H=[];R=[];n=d
    for cols in rows:
        mask=0
        for a,b in cols:
            H.append(((1<<n)^a,b));mask|=1<<n;n+=1
        R.append(mask)
    return n,tuple(R),canon(H)


def main():
    rng=Random(3692713);hist=Counter();examples={}
    for d in range(2,9):
        for _ in range(120):
            F=tuple(canon(((a,rng.randrange(2)),(b,rng.randrange(2)))) for a,b in
                (rng.sample(range(1,1<<d),2) for j in range(rng.randrange(1,13))))
            truth=[z for z in range(1<<d) if satisfies(z,(),F)]
            H,t,S=deduce(F,[],Budget(10**9))
            assert H is not None or not truth
            assert H is None or all(satisfies(z,H,()) for z in truth)
            assert all(satisfies(z,(),S)==satisfies(z,(),F) for z in range(1<<d))
            hist['flat_sources']+=1;hist['flat_empty_truth']+=not truth
            hist['flat_cert_empty']+=H is None;hist['flat_forced']+=bool(H);hist['flat_stall']+=H==()
            hist['flat_refutations']+=len(t)
            for _,why in t:hist['flat_'+why]+=1
    for d in range(2,7):
        for _ in range(100):
            M=[];caps=[]
            for j in range(rng.randrange(2,5)):
                k=rng.randrange(2,7);m={0:2+2*k}
                for i in range(k):add(m,rng.randrange(1,1<<d),rng.choice((-2,2)))
                M.append(m);caps.append(rng.choice(range(1,2*k+2,2)))
            P=portfolio(M,caps,Budget(10**9))
            truth=[z for z in range(1<<d) if all(evaluate(m,z)<=2*c for m,c in zip(M,caps))]
            Q,rec,count=observe(P,Budget(10**9))
            F=verify_receipts(P,rec,Budget(10**9));assert all(satisfies(z,(),F) for z in truth)
            hist['capacity_sources']+=1;hist['capacity_empty_truth']+=not truth
            hist['capacity_unique']+=len(truth)==1
            if Q is None:
                assert not truth;hist['capacity_observer_empty']+=1;continue
            assert all(satisfies(z,Q,()) for z in truth)
            H,t,S=deduce(F,P,Budget(10**9),Q)
            assert H is not None or not truth
            assert H is None or all(satisfies(z,H,()) for z in truth)
            hist['capacity_receipts']+=len(F);hist['capacity_collector_empty']+=H is None
            hist['capacity_gain']+=H is None or len(H)>len(Q)
            if Q==():
                hist['capacity_rank2_stall']+=1
                if H!=():
                    hist['capacity_rank2_stall_gain']+=1
                    examples.setdefault('gain',dict(M=M,caps=caps,truth=truth,base=Q,result=H,trace=t))
            for _,why in t:hist['capacity_'+why]+=1
    F=tuple(canon(G) for G in (((1,0),(2,1)),((1,0),(4,1)),((1,0),(6,0))))
    assert propagate(F,((1,0),),[],Budget(10**9))==(None,'parity_conflict')
    assert deduce(F,[],Budget(10**9))[0]==((1,1),)
    chains=[]
    for d in (4,8,16,32,64):
        F=tuple(canon(((1<<i,0),(1<<(i+1),1))) for i in range(d-1))
        P=[({0:2+2*d,**{1<<i:2 for i in range(d)}},1+2*(d-1),1,(0,))]
        assert propagate(F,((1,0),),P,Budget(10**9))==(None,'conditioned_floor')
        H,t,S=deduce(F,P,Budget(10**9))
        assert H is not None and satisfies((1<<d)-1,H,()) and (1,1) in H
        chains.append(dict(dimension=d,rank=len(H),refutations=len(t)))
    rng=Random(3692714);screen_hist=Counter()
    for d in range(2,7):
        for _ in range(80):
            rows=[];caps=[]
            for j in range(rng.randrange(2,5)):
                k=rng.randrange(2,7);cols=[(0,1)]
                for i in range(k):cols.extend([(rng.randrange(1,1<<d),rng.randrange(2))]*2)
                rows.append(cols);caps.append(rng.choice(range(1,2*k+2,2)))
            n,R,H=original(d,rows);u,V=chart(n,H)
            truth=[lift(u,V,z) for z in range(1<<d) if all((lift(u,V,z)&r).bit_count()<=c for r,c in zip(R,caps))]
            audit=[];K,y,why=screen(n,R,H,caps,Budget(10**9),audit=audit)
            screen_hist[why]+=1;screen_hist['truth_empty']+=not truth
            if K is None:assert not truth
            else:assert all(satisfies(x,K,()) for x in truth)
            if y is not None:
                assert y in truth;A=Matrix(len(R),n,lambda i,j:R[i]>>j&1)
                assert all(v<=c and v%2==1 for v,c in zip(A*Matrix([y>>j&1 for j in range(n)]),caps))
            if why=='imp_stalled':screen_hist['stalled_empty']+=not truth
    here=Path(__file__).parent;files=sorted(here.glob('check_pnp_*.py'))
    key=hashlib.sha256(b''.join(p.name.encode()+b'\0'+p.read_bytes() for p in files)).hexdigest()
    result=dict(key=key,counts=dict(hist),chains=chains,screen=dict(screen_hist),examples=examples)
    out=Path(sys.argv[1]);out.parent.mkdir(parents=True,exist_ok=True);tmp=out.with_suffix('.tmp')
    tmp.write_text(json.dumps(result,indent=2));os.replace(tmp,out);print(result)
if __name__=='__main__':main()
