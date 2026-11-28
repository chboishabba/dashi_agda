"""Independent connected sources; exhaustive oracle only on small fixtures."""
from random import Random
from itertools import product
from collections import Counter
from check_pnp_normal_endpoint_weld import normal_probe,normal_clipped,exact_cover,cnf_solver
from check_p0_signed_contrast_20261125 import ContinuationAllowance
from check_pnp_endpoint_portfolio import cnf_solver as prior_solver
from check_pnp_endpoint_live_fold import solve as live


def main():
    rng=Random(3693001);C=Counter()
    for n in range(9):
        for _ in range(32):
            F=tuple(tuple(rng.choice((-1,1))*rng.randrange(1,n+1) for _ in range(rng.randrange(5))) for _ in range(rng.randrange(8))) if n else ((),) if rng.randrange(2) else ()
            H=tuple((rng.randrange(1<<n),rng.randrange(2)) for _ in range(rng.randrange(4)))
            W=[x for x in product((0,1),repeat=n) if all(any(x[abs(l)-1]==int(l>0) for l in c) for c in F) and all(sum(b for i,b in enumerate(x) if a>>i&1)%2==v for a,v in H)]
            root=ContinuationAllowance(1000000);q=normal_clipped(F,n,H,root,1000000);assert q['count']==min(2,len(W))
            if W:assert q['witness'] in W
            if len(W)>1:assert q['other'] in W and q['other']!=q['witness']
            assert sum(root.charges.values())+root.left==root.total;C['clipped']+=1
    for _ in range(240):
        n=rng.randrange(1,13);m=rng.choice((3,6,9,12));S=[tuple(rng.sample(range(m),3)) for i in range(n)]
        O=tuple(tuple(j for j,s in enumerate(S) if i in s) for i in range(m));W=[x for x in product((0,1),repeat=n) if all(sum(x[i] for i in c)==1 for c in O)]
        q=exact_cover(O,n,ContinuationAllowance(1000000),1000000)
        assert q['status']==('WITNESS' if W else 'EMPTY')
        if W:assert q['witness'] in W
        C['x3c']+=1
    # Connected random 3-CNF, no planted solution, with chain backbone.
    # Bound each actual solver separately for comparison; same truth oracle.
    for n in (10,12,14):
        for _ in range(12):
            F=tuple(tuple(rng.choice((-1,1))*(v+1) for v in (i,(i+1)%n,(i+2)%n)) for i in range(n))+tuple(tuple(rng.choice((-1,1))*(v+1) for v in rng.sample(range(n),3)) for j in range(3*n))
            W=[x for x in product((0,1),repeat=n) if all(any(x[abs(l)-1]==int(l>0) for l in c) for c in F)]
            for name,fn in (('prior',prior_solver),('integrated',cnf_solver)):
                q=fn(F,n,(),(),20000)
                if q['status']=='WITNESS':assert q['witness'] in W
                if q['status']=='EMPTY':assert not W
                C[name,q['status']]+=1
                if name=='prior':old=q['status']
                else:C['transition',old,q['status']]+=1
    # Distinct triples in cyclic 3D matching. High-width, connected, no duplicates.
    for k in (3,4,5,6):
        S=[(i,k+j,2*k+(i+j)%k) for i in range(k) for j in range(k)];O=tuple(tuple(j for j,s in enumerate(S) if i in s) for i in range(3*k))
        q=exact_cover(O,k*k,ContinuationAllowance(100000),100000)
        if q['status']=='WITNESS':assert k%2 and all(sum(q['witness'][i] for i in c)==1 for c in O)
        if q['status']=='EMPTY':assert k%2==0
        print('latin',k,q['status'],q.get('width'))
    q=normal_clipped(((1,),),1,(),ContinuationAllowance(0),0,known=(1,));assert q['status']=='UNKNOWN' and q['witness']==(1,) and q['lower']==1
    assert exact_cover(((0,),),1,ContinuationAllowance(0),0)['status']=='UNKNOWN'
    print(dict(C))
if __name__=='__main__':main()
