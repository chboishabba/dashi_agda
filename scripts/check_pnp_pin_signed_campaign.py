"""Metered original pin solver and signed prefix enclosure checks."""
from collections import Counter
from itertools import product
from random import Random
from check_pnp_affine_pin_dispatch import solve_pins
from check_pnp_bit_data_schedule import Clock
from check_pnp_mobius_prefix import prefix_contrast


def main():
    rng=Random(36943);C=Counter();data=Clock(10**8)
    for n in range(9):
        for k in range(16):
            F=tuple(tuple((i+1)*rng.choice((-1,1)) for i in rng.sample(range(n),rng.randrange(min(n,4)+1))) for _ in range(k%7))
            rows=(tuple(rng.randrange(3) for i in range(n)),)
            for t in range(3):
                W=[x for x in product((0,1),repeat=n) if all(any(x[abs(l)-1]==int(l>0) for l in c) for c in F) and sum(a*b for a,b in zip(rows[0],x))%3==t]
                for cap in (0,4096,10**7):
                    q=solve_pins(F,n,rows,(t,),cap,data_clock=data);s=q['status'];C[cap,s]+=1
                    assert q['reserved']<=cap
                    if s=='WITNESS':assert q['witness'] in W
                    if s=='EMPTY':assert not W
                    if 'count' in q:assert q['count']==len(W)
    assert C[4096,'WITNESS']==172 and C[4096,'EMPTY']==249 and C[4096,'UNKNOWN']==11
    assert C[10**7,'WITNESS']==183 and C[10**7,'EMPTY']==249
    print(dict(pin_cases=sum(C.values()),pin_charged=data.cap-data.left,counts=dict(C)))
    rng=Random(36927);data=Clock(10**8);tested=refused=0
    for n in range(1,7):
        for k in range(16):
            F=tuple(tuple((i+1)*rng.choice((-1,1)) for i in rng.sample(range(n),rng.randrange(1,min(n,3)+1))) for _ in range(5))
            cols=tuple((rng.randrange(3),rng.randrange(3)) for i in range(n));t=(rng.randrange(3),);w=rng.choice((-3,-1,1,4));H=[0]*3
            for x in product((0,1),repeat=n):
                if all(any(x[abs(l)-1]==int(l>0) for l in c) for c in F) and sum(a[0]*b for a,b in zip(cols,x))%3==t[0]:H[sum(a[1]*b for a,b in zip(cols,x))%3]+=1
            truth=tuple(w*(3*h-sum(H)) for h in H)
            for cap in (0,256,4096,100000):
                q=prefix_contrast(F,cols,t,0,range(n),w,work_cap=100000,data_clock=Clock(cap))
                if q is None:refused+=1
                else:assert all(a<=v<=b for a,v,b in zip(q[0],truth,q[1]))
                tested+=1
            q=prefix_contrast(F,cols,t,0,range(n),w,work_cap=100000,data_clock=data)
            ref=prefix_contrast(F,cols,t,0,range(n),w,work_cap=100000)
            assert q is not None and q[:2]==ref[:2] and q[0]==truth==q[1]
    print(dict(prefix_clock_controls=tested,refused=refused,exact=96,prefix_charged=data.cap-data.left))
if __name__=='__main__':main()
