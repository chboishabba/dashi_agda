"""Six-face signed cube and complete original 60-source continuation replay.

Run locally with a 90s timeout; per-source atomic checkpoints. No CI.
A refused producer is UNKNOWN. Original witnesses checked by integer matrix.
"""
from pathlib import Path
from random import Random
from collections import Counter
import json,sys,hashlib,os
from sympy import Matrix
from check_pnp_affine_normal_components import canon,chart,satisfies,Budget
from check_pnp_demand_strata import Allowance
from check_pnp_capacity_partition import partition
from check_pnp_signed_capacity_square import add,bounds,pin_pull,evaluate
from check_pnp_signed_capacity_cube import restrict_ledger,pin_floors

HERE=Path(__file__).parent

def reduce_pair(a,b,H):
    for r,s in H:
        if a&(1<<(r.bit_length()-1)):a^=r;b^=s
    return a,b

def raw(cols,H):
    H=canon(H)
    return None if H is None else [reduce_pair(a,b,H) for a,b in cols]

def group(cols):
    M={0:2}
    for a,b in cols:add(M,0,1);add(M,a,1 if b else -1)
    return M

def faces():
    rng=Random(3692711);stats=Counter()
    for n in range(1,9):
        for _ in range(180):
            cols=[]
            for j in range(rng.randrange(1,10)):
                a=rng.randrange(1<<n);b=rng.randrange(2)
                cols.extend([(a,b),(a,b)])
            M=group(cols);F=pin_floors(M)
            for a in range(1,1<<n):
                for b in (0,1):
                    Q=restrict_ledger(M,((a,b),))
                    assert Q==pin_pull(M,a,b)
                    assert F.get(a,(bounds(M)[0],)*2)[b]==bounds(Q)[0]
                    stats['pin_floors']+=1
            a,b=rng.randrange(1,1<<n),rng.randrange(1,1<<n)
            x,y=rng.randrange(2),rng.randrange(2)
            A=((a,x),);B=((b,y),);H=canon(A+B);Q=restrict_ledger(M,A+B)
            for first,second in ((A,B),(B,A)):
                K=(reduce_pair(*second[0],first),)
                assert restrict_ledger(restrict_ledger(M,first),K)==Q
                stats['signed_faces']+=1
                assert group(raw(cols,first))==restrict_ledger(M,first)
                stats['group_faces']+=1
            if H is None:
                assert raw(cols,A+B) is None and Q is None
                stats['contradictions']+=1
            else:
                assert group(raw(cols,A+B))==Q
                for first,second in ((A,B),(B,A)):
                    K=(reduce_pair(*second[0],first),)
                    assert raw(raw(cols,first),K)==raw(cols,A+B)
                    assert group(raw(raw(cols,first),K))==restrict_ledger(group(raw(cols,first)),K)==Q
                    stats['conditioned_faces']+=1
                stats['original_faces']+=1
                for z in range(1<<n):
                    if satisfies(z,H,()):
                        assert evaluate(M,z)==evaluate(Q,z)
                        stats['point_checks']+=1
    # A genuine extra normal absent from the ledger; old screen stalls.
    M={0:10,2:-1,3:-2,5:-1,1:1,6:1,7:2}
    assert bounds(M)[0]<=3 and all(bounds(pin_pull(M,a,b))[0]<=3 for a in M if a for b in (0,1))
    assert 4 not in M and pin_floors(M)[4]==(5,1)
    assert [z for z in range(8) if evaluate(M,z)<=6]==[4,7]
    return dict(stats)

def fixture(m,degree,seed):
    rng=Random(3692700+100*m+10*degree+seed);S=[]
    for _ in range(degree):
        for attempt in range(1000):
            p=list(range(m));rng.shuffle(p);T=[tuple(sorted(p[i:i+3])) for i in range(0,m,3)]
            if not set(T)&set(S):break
        else:raise AssertionError('fixture generation cap')
        S.extend(T)
    rng.shuffle(S);n=len(S);R=tuple(sum(1<<j for j,T in enumerate(S) if i in T) for i in range(m))
    return n,R,canon(tuple((r,1) for r in R))

def main():
    path=Path(sys.argv[1]);files=sorted(HERE.glob('check_pnp_*.py'))
    key=hashlib.sha256(b''.join(p.name.encode()+b'\0'+p.read_bytes() for p in files)).hexdigest()
    state=json.loads(path.read_text()) if path.exists() else dict(key=key,faces=faces(),cases=[])
    assert state['key']==key
    seen={r['name'] for r in state['cases']}
    for m in (18,24,30,36,42):
        for degree in (5,7,9):
            for seed in range(4):
                name=f'{m}_{degree}_{seed}'
                if name in seen:continue
                n,R,H=fixture(m,degree,seed);A=Matrix(m,n,lambda i,j:R[i]>>j&1)
                row=dict(name=name,n=n,dimension=n-len(H),lanes={})
                for label,mode in (('baseline',False),('square',True),('cube','cube')):
                    B=Budget(20_000_000)
                    z=partition(n,R,H,(1,)*m,Allowance(B,B.left),nodes=256,signed_screen=mode)
                    assert z.upper>0 # planted, no planted witness supplied
                    if z.witness is not None:
                        assert satisfies(z.witness,H,()) and all(v==1 for v in A*Matrix([z.witness>>j&1 for j in range(n)]))
                    row['lanes'][label]=dict(witness=None if z.witness is None else str(z.witness),steps=z.stage,upper=str(z.upper),charged=sum(B.stats.values()),charges=dict(B.stats))
                state['cases'].append(row);path.parent.mkdir(parents=True,exist_ok=True)
                tmp=path.with_suffix('.tmp');tmp.write_text(json.dumps(state,indent=2));os.replace(tmp,path)
                print(name,[(k,v['witness'] is not None,v['charged']) for k,v in row['lanes'].items()],flush=True)
    print('sources',len(state['cases']),'faces',state['faces'])
if __name__=='__main__':main()
