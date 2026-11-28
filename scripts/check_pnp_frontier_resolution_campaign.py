"""Independent original source truth oracles, including unique connected sources."""
from check_pnp_frontier_resolution import *
from check_pnp_normal_endpoint_weld import normal_clipped
from itertools import product,combinations
from random import Random
from collections import Counter

def main():
    rng=Random(3693101);C=Counter();max_proof=0
    for n in range(8):
        for _ in range(48):
            F=tuple(tuple(rng.choice((-1,1))*rng.randrange(1,n+1) for _ in range(rng.randrange(5))) for _ in range(rng.randrange(10))) if n else ((),) if rng.randrange(2) else ()
            W=[x for x in product((0,1),repeat=n) if accepts(F,x)]
            for cap in (0,256,1000000):
                q=learn(F,n,cap);D=replay(F,n,q['proof'],Reservation(10**7));assert D is not None and q['used']<=cap
                if q['status']=='EMPTY':assert not W and D[q['empty_id']]==()
                elif q['status']=='WITNESS':assert q['witness'] in W
                if cap==1000000:assert q['status']==('WITNESS' if W else 'EMPTY')
                for c in D:assert all(accepts((c,),x) for x in W)
                C['small']+=1;max_proof=max(max_proof,len(q['proof']))
    # Independently choose unique original sources by exhaustive oracle;
    # the solver receives only the source and known original anchor.
    for n in (10,12):
        found=0;attempt=0
        while found<12 and attempt<300:
            attempt+=1
            F=tuple(tuple(rng.choice((-1,1))*(v+1) for v in (i,(i+1)%n,(i+2)%n)) for i in range(n))+tuple(tuple(rng.choice((-1,1))*(v+1) for v in rng.sample(range(n),3)) for j in range(3*n))
            W=[x for x in product((0,1),repeat=n) if accepts(F,x)]
            if len(W)!=1:continue
            found+=1;anchor=W[0];G=F+(tuple((i+1)*(1-2*b) for i,b in enumerate(anchor)),)
            old=live(G,n,(),(),(),20000,clip=2);q=puncture(F,n,anchor,20000)
            r=normal_clipped(F,n,(),ContinuationAllowance(20000),20000,known=anchor)
            C['unique_live',old['status']]+=1;C['unique_learning',q['status']]+=1;C['unique_normal',r['status']]+=1
            if q['status']=='COMPLETE':assert q['count']==1
            if r['status']=='COMPLETE':assert r['count']==1
            if old['status']!='UNKNOWN':assert old['status']=='EMPTY'
        assert found==12,(n,found,attempt)
    # Original exact cover instances, every column a distinct triple.
    # Random 3D matching with planted diagonal plus independently sampled
    # additional triples. Check uniqueness before calling the puncture.
    for k in (3,4):
        found=0;attempt=0
        while found<12 and attempt<200:
            attempt+=1
            S=tuple((i,k+i,2*k+i) for i in range(k));pool=[(i,k+j,2*k+h) for i,j,h in product(range(k),repeat=3) if (i,k+j,2*k+h) not in S]
            S+=tuple(rng.sample(pool,2*k));n=len(S);O=tuple(tuple(j for j,s in enumerate(S) if i in s) for i in range(3*k))
            F=tuple(tuple(i+1 for i in c) for c in O)+tuple((-(i+1),-(j+1)) for c in O for i,j in combinations(c,2))
            W=[x for x in product((0,1),repeat=n) if all(sum(x[i] for i in c)==1 for c in O)]
            if len(W)!=1:continue
            found+=1;anchor=W[0];G=F+(tuple((i+1)*(1-2*b) for i,b in enumerate(anchor)),)
            old=live(G,n,(),(),(),20000,clip=2);q=puncture(F,n,anchor,20000)
            C['x3c_live',old['status']]+=1;C['x3c_learning',q['status']]+=1
            if q['status']=='COMPLETE':assert q['count']==1
            if old['status']!='UNKNOWN':assert old['status']=='EMPTY'
        assert found==12
    F=((1,),(-1,));q=learn(F,1,1000);p=q['proof'];assert p
    assert replay(F,1,p[:-1]+((p[-1][0],p[-1][1],p[-1][2],(1,)),),Reservation(1000)) is None
    assert puncture(((1,),),1,(1,),0)['status']=='UNKNOWN'
    print(dict(C), 'max_proof',max_proof,'tamper/refusal PASS')
if __name__=='__main__':main()
