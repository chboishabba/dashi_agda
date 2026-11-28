"""Bounded integrated original-CNF cover/frontier/prefix campaign."""
from check_pnp_source_derived_cover import source_solve
from collections import Counter
from itertools import product
from random import Random

def check(F,n,rows,t,cap,**kw):
    W=[x for x in product((0,1),repeat=n) if all(any(x[abs(l)-1]==int(l>0) for l in c) for c in F)
       and tuple(sum(a*b for a,b in zip(row,x))%3 for row in rows)==t]
    q=source_solve(F,n,rows,t,cap,**kw)
    assert q['reserved']<=cap
    if q['status']=='WITNESS':assert q['witness'] in W
    if q['status']=='EMPTY':assert not W
    if q['status']=='POSITIVE_NO_LIFT':assert W
    if 'count' in q:assert q['count']==len(W)
    if cap>=10**7:assert q['status']==('WITNESS' if W else 'EMPTY'),(n,t,q)
    return q

def main():
    rng=Random(36943);C=Counter()
    for n in range(9):
        for k in range(16):
            F=tuple(tuple((i+1)*rng.choice((-1,1)) for i in rng.sample(range(n),rng.randrange(min(n,4)+1))) for _ in range(k%7))
            rows=(tuple(rng.randrange(3) for i in range(n)),)
            for t in range(3):
                for cap in (0,4096,10**7):
                    q=check(F,n,rows,(t,),cap)
                    C[cap,q['status']]+=1
    # Complete primal graph, distinct affine columns prohibit all twins.
    n=6;F=tuple((i+1,j+1) for i in range(n) for j in range(i+1,n))
    rows=tuple(tuple(int(i==j) for i in range(n)) for j in range(n))
    for x in ((1,)*n,(0,)*n,(0,1,1,1,1,1)):
        q=check(F,n,rows,x,10**7,max_width=3,pin_width=2)
        assert q['high_fill'] and q['pins']==(0,1)
        C['high_fill',q['status']]+=1
    print(dict(C))
if __name__=='__main__':main()
