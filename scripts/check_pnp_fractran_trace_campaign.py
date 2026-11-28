"""Bounded independent original-coordinate receipt checks."""
from random import Random
from check_pnp_affine_normal_components import Budget, Exhausted, canon, chart, lift, satisfies
from check_pnp_fractran_trace import trace, recover_trace, improve_trace

def main():
    rng=Random(369); receipts=units=refusals=0
    for n in range(1,9):
        for _ in range(160):
            a=rng.randrange(1<<n)
            H=canon(tuple((q,(q&a).bit_count()%2) for q in (rng.randrange(1<<n) for _ in range(n//2))))
            u,V=chart(n,H)
            x,y=(lift(u,V,rng.randrange(1<<len(V))) for _ in range(2))
            R=tuple(rng.randrange(1<<n) for _ in range(8))
            caps=tuple(rng.randrange(n+1) for _ in R)
            phi=lambda z:sum(max(0,(r&z).bit_count()-c) for r,c in zip(R,caps))
            t=trace(n,R,H,caps,x,y,Budget(1000000))
            assert (t is not None)==(phi(y)<phi(x))
            if t is None:refusals+=1;continue
            receipts+=1;assert t['decrease']==phi(x)-phi(y)
            assert len(t['macros'])<=len(V)
            z=x
            for m in t['macros']:
                assert m['before']==z
                for q in m['units']:
                    i=q['coord'];assert q['denominator']==(i,(z>>i)&1)
                    z^=1<<i;units+=1
                    assert q['state']==z and q['numerator']==(i,(z>>i)&1)
                    assert q['residual']==tuple((r&z).bit_count()-c for r,c in zip(R,caps))
                assert z==m['after'] and satisfies(z,H,())
            assert z==y
    # Odd-row onehot instance: source has three ones; target has one.
    t=recover_trace(3,(7,),((7,1),),(1,),7,Budget(1000000))
    assert t is not None and t['decrease']==2
    # Nonlinear prefix blocked: endpoints 00 and 11, canonical prefix 01.
    assert trace(2,(3,),(),(0,),3,0,Budget(100000),(((1,0),(2,1)),)) is None
    try:trace(3,(7,),(),(0,),7,0,Budget(0))
    except Exhausted:pass
    else:raise AssertionError('budget refusal')
    # Compare completed aggregate minima to exhaustive original points.
    folds=0
    for n in range(1,8):
        for _ in range(60):
            x=rng.randrange(1<<n)
            R=tuple(r for r in range(1,1<<n) if (r&x).bit_count()%2)
            if not R:continue
            R=tuple(rng.sample(R,min(8,len(R))))
            union=0
            for r in R:union|=r
            if union!=(1<<n)-1:continue
            H=canon(tuple((r,1) for r in R))
            caps=tuple(rng.randrange(1,n+1) for r in R)
            phi=lambda z:sum(max(0,(r&z).bit_count()-c) for r,c in zip(R,caps))
            best=min(phi(z) for z in range(1<<n) if satisfies(z,H,()))
            status,t,lower=improve_trace(n,R,H,caps,x,Budget(10000000))
            assert status!='UNKNOWN'
            assert lower==best
            if phi(x)==0:assert status=='SAT'
            elif best==phi(x):assert status=='MINIMUM'
            else:assert status=='IMPROVED' and phi(t['end'])==best
            folds+=1
    # Hard nonlinear leaves, free coordinates and atomic semantics.
    from check_pnp_separator_row_strata import build, minimum_excess
    hard_cases=0
    for n in range(2,8):
        for _ in range(60):
            x=rng.randrange(1,1<<n)
            R=tuple(r for r in range(1,1<<n) if (r&x).bit_count()%2)
            R=tuple(rng.sample(R,min(4,len(R))))
            H=canon(tuple((r,1) for r in R))
            caps=tuple(rng.randrange(n+1) for r in R)
            F=[]
            for k in range(3):
                a,b=rng.sample(range(n),2)
                F.append(((1<<a,rng.randrange(2)),(1<<b,rng.randrange(2))))
            F=tuple(F)
            phi=lambda z:sum(max(0,(r&z).bit_count()-c) for r,c in zip(R,caps))
            truth=[phi(z) for z in range(1<<n) if satisfies(z,H,F)]
            B=Budget(10000000)
            G=build(n,R,H,B,hard_flats=F)
            assert G is not None
            v,y=minimum_excess(n,R,H,caps,G,B,hard_flats=F)
            assert (v is None)==(not truth)
            if truth:assert v==min(truth) and satisfies(y,H,F)
            hard_cases+=1
    F=(((1,0),(2,1)),)
    assert trace(2,(3,),(),(0,),3,0,Budget(100000),F) is None
    t=trace(2,(3,),(),(0,),3,0,Budget(100000),F,atomic_basis_block=True)
    assert t is not None and len(t['macros'])==1 and len(t['macros'][0]['units'])==2
    print('aggregate fold cases',folds,'hard cases',hard_cases)
    print(dict(receipts=receipts,units=units,nonimprovement=refusals,controls='PASS'))

if __name__=='__main__':main()
