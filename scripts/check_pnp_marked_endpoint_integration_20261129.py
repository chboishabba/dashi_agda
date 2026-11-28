#!/usr/bin/env python3
"""Full-checkout opt-in integration acceptance. Run under timeout 90s, no CI."""
from itertools import product
from random import Random
from check_pnp_affine_normal_components import Budget, canon
from check_pnp_demand_strata import Allowance
from check_pnp_capacity_signed import observe
from check_pnp_normal_mass import count
from check_pnp_normal_endpoint_weld import normal_clipped
from check_p0_signed_contrast_20261125 import ContinuationAllowance


def main():
    rng=Random(5004); checks=0
    for n in range(1,7):
        for _ in range(24):
            F=tuple(tuple(rng.choice((-1,1))*i for i in rng.sample(range(1,n+1),rng.randrange(min(3,n)+1))) for _ in range(rng.randrange(7)))
            H=canon(tuple((rng.randrange(1<<n),rng.randrange(2)) for _ in range(2)))
            if H is None:continue
            W=[x for x in product((0,1),repeat=n) if all(sum(x[i] for i in range(n) if r>>i&1)%2==b for r,b in H) and all(any(x[abs(l)-1]==int(l>0) for l in c) for c in F)]
            for known in (None,W[0] if W else None):
                root=ContinuationAllowance(10**7);q=normal_clipped(F,n,H,root,10**7,known,marked=True)
                assert q['count']==min(2,len(W)) and root.left==0
                if W:assert q['witness'] in W
                if len(W)>1:assert q['other'] in W and q['other']!=q['witness']
                checks+=1
            if W:
                root=ContinuationAllowance(1);q=normal_clipped(F,n,H,root,1,W[0],marked=True)
                assert q['status']=='UNKNOWN' and q['witness']==W[0] and (q['lower'],q['upper'])==(1,2) and root.left==0
    # Actual source odd parity and exact-one capacity, all original normal channels.
    S=[(2,10,15),(7,9,12),(3,4,14),(0,6,16),(1,5,13),(8,11,17),(9,15,16),(0,8,14),(2,6,17),(5,10,13),(1,3,12),(4,7,11),(3,11,12),(1,2,6),(0,7,14),(4,9,15),(10,13,17),(5,8,16),(0,1,14),(4,9,16),(7,12,15),(2,5,17),(3,6,11),(8,10,13),(0,1,9),(4,11,17),(3,6,16),(2,10,12),(5,14,15),(7,8,13)]
    R=tuple(sum(1<<j for j,s in enumerate(S) if i in s) for i in range(18));H=canon((r,1) for r in R);O=tuple(tuple((1<<i,0) for i in range(30) if r>>i&1) for r in R)
    W=(63,100663443,4032,201375792,258048,16515072,1056964608)
    q=count(30,H,(),O,200000000,marks=tuple(1<<i for i in range(30)))
    assert q['count']==7
    for i,channels in enumerate(q['marginals']):
        assert tuple(a for a,_ in channels)==tuple(sum((x>>i&1)==b for x in W) for b in (0,1))
    for i in (0,4,14,26):
        B=Budget(100000000);A=Allowance(B,100000000);I=observe(30,R,H,(1,)*18,A,1<<i,marked_budget=50000000)
        assert B.stats['capacity_marked_reservation']==50000000 and B.left==50000000 and A.left==50000000
        for b,v in enumerate(I):
            c=sum((x>>i&1)==b for x in W)
            assert v.lower==v.upper==c and v.witness in W and (v.witness>>i&1)==b
            checks+=1
    print(dict(status='PASS',checks=checks,original_channels=60))


if __name__=='__main__':main()
