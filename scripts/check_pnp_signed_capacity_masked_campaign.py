"""Local exact acceptance for scoped masked minima and original reopening.

Run: python scripts/check_pnp_signed_capacity_masked_campaign.py receipt.json
Truth enumeration is isolated here and never supplied to a producer.
"""
from collections import Counter
from random import Random
from pathlib import Path
import hashlib,json,os,sys
from sympy import Matrix
from check_pnp_affine_normal_components import Budget, Exhausted, canon, chart, lift, satisfies
from check_pnp_signed_capacity_square import evaluate
from check_pnp_signed_capacity_implication_campaign import original
from check_pnp_signed_capacity_masked import masked_minimum, capacity_join, screen


def main():
    rng=Random(3692715);hist=Counter();sources=[]
    for n in range(1,7):
        for _ in range(60):
            F=tuple(G for j in range(rng.randrange(7))
                    if (G:=canon((rng.randrange(1,1<<n),rng.randrange(2))
                    for k in range(rng.randrange(1,4)))) is not None)
            M=[{a:rng.randrange(-8,9) for a in rng.sample(range(1<<n),
                 rng.randrange(1,min(9,1<<n)+1))} for j in range(rng.randrange(1,4))]
            caps=[rng.randrange(-4,5) for m in M]
            allowed=[z for z in range(1<<n) if satisfies(z,(),F)]
            for m in M:
                want=min((evaluate(m,z) for z in allowed),default=None)
                done,c,z,w=masked_minimum(n,m,F,Budget(10**8),n)
                assert done and c==want and (z is None)==(want is None)
                if z is not None:assert z in allowed and evaluate(m,z)==want
                hist['masked_minimum']+=1
                if allowed:hist['tightened']+=want>min(evaluate(m,z) for z in range(1<<n))
                done,c,z,w=masked_minimum(n,m,F,Budget(10**8),0)
                if not done:assert c is None and z is None;hist['width_refusal']+=1
            truth=[z for z in allowed if all(evaluate(m,z)<=2*c for m,c in zip(M,caps))]
            done,z,w=capacity_join(n,M,caps,F,Budget(10**8),n)
            assert done and (z is not None)==bool(truth)
            if z is not None:assert z in truth
            hist['joint']+=1;hist['joint_empty']+=not truth
    # Independent row minimizers cannot be glued into a joint witness.
    assert capacity_join(1,[{0:1,1:1},{0:1,1:-1}],[0,0],(),Budget(10000),1)[:2]==(True,None)
    assert masked_minimum(0,{0:-7},(),Budget(10000),0)[:3]==(True,-7,0)
    assert masked_minimum(0,{0:3},((),),Budget(10000),0)[:3]==(True,None,None)
    try:masked_minimum(2,{1:1},(),Budget(0),2)
    except Exhausted:hist['budget_refusal']+=1
    else:raise AssertionError('budget refusal')
    # High ambient rank, genuinely independent rank-one row factors.
    for n in (8,16,32,64):
        M=[{0:1,1<<i:1} for i in range(n)]
        B=Budget(10**8);done,z,w=capacity_join(n,M,[0]*n,(),B,1)
        assert done and z==(1<<n)-1 and w==1
        sources.append(dict(kind='independent_rank',dimension=n,width=w,charges=dict(B.stats)))
    # Exact previous 400-source original-coordinate campaign.
    rng=Random(3692714)
    from check_pnp_signed_capacity_implication import screen as old
    for d in range(2,7):
        for i in range(80):
            cols=[];caps=[]
            for j in range(rng.randrange(2,5)):
                k=rng.randrange(2,7);C=[(0,1)]
                for t in range(k):C.extend([(rng.randrange(1,1<<d),rng.randrange(2))]*2)
                cols.append(C);caps.append(rng.choice(range(1,2*k+2,2)))
            n,R,H=original(d,cols);u,V=chart(n,H)
            truth=[lift(u,V,z) for z in range(1<<d) if all((lift(u,V,z)&r).bit_count()<=c for r,c in zip(R,caps))]
            K,y,why=old(n,R,H,caps,Budget(10**9))
            hist['prior_'+why]+=1
            if why!='imp_stalled':continue
            audit=[];B=Budget(10**9);K,y,why=screen(n,R,H,caps,B,width=6,audit=audit)
            hist['reopen_'+why]+=1
            assert K is not None or not truth
            if y is not None:
                assert y in truth
                A=Matrix(len(R),n,lambda j,k:R[j]>>k&1)
                assert all(v<=c and v%2==1 for v,c in zip(A*Matrix([y>>k&1 for k in range(n)]),caps))
            assert why!='masked_width_refusal' # chart dimensions at most six
            assert (y is not None)==bool(truth)
            sources.append(dict(kind='prior_stall',dimension=d,index=i,reason=why,
                 residual=n-len(K) if K is not None else None,
                 flats=len(next(a for a in reversed(audit) if 'retained_original_flats' in a)['retained_original_flats']),
                 widths=[a['width'] for a in audit if 'width' in a],charges=dict(B.stats)))
    assert hist['prior_imp_stalled']==52 and hist['reopen_masked_joint_witness']==52
    here=Path(__file__).parent
    key=hashlib.sha256(b''.join(p.name.encode()+b'\0'+p.read_bytes() for p in sorted(here.glob('check_pnp_*.py')))).hexdigest()
    receipt=dict(source_hash=key,counts=dict(hist),sources=sources)
    out=Path(sys.argv[1]);out.parent.mkdir(parents=True,exist_ok=True)
    tmp=out.with_suffix('.tmp');tmp.write_text(json.dumps(receipt,indent=2));os.replace(tmp,out)
    print(dict(hist))

if __name__=='__main__':main()
