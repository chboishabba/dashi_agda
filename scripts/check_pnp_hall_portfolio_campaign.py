"""Source-native Hall retirement with extra constraints and typed endpoint replay."""
from itertools import product,combinations
from random import Random
from collections import Counter
from check_pnp_hall_geometry import cnf_hall,cnf_solver,verify_partition,Reservation
from check_pnp_frontier_resolution import accepts
from check_pnp_normal_endpoint_weld import cnf_solver as prior
from check_pnp_typed_portfolio import cnf_dispatch,hard_dispatch,satisfies
from check_p0_signed_contrast_20261125 import ContinuationAllowance


def main():
    rng=Random(3693202);C=Counter()
    for k in (2,3,4):
        for _ in range(48):
            E=tuple((i,j) for i in range(k) for j in range(k) if rng.random()<.55)
            if len(E)>14:continue
            n=len(E);row=tuple(tuple(t+1 for t,(i,j) in enumerate(E) if i==a) for a in range(k));col=tuple(tuple(t+1 for t,(i,j) in enumerate(E) if j==a) for a in range(k))
            F=row+tuple((-a,-b) for c in col for a,b in combinations(c,2))
            if n:F+=tuple(tuple(rng.choice((-1,1))*rng.randrange(1,n+1) for _ in range(3)) for _ in range(2))
            W=[x for x in product((0,1),repeat=n) if accepts(F,x)]
            q=cnf_hall(F,n,10**7,contract=True)
            if q['status']=='EMPTY':assert not W
            else:
                assert q['status']=='RESIDUAL';assert verify_partition(F,n,q['rows'],q['cols'],Reservation(10**7))
                assert all(accepts(q['units'],x) for x in W)
                C['units']+=len(q['units']);C['receipts']+=len(q['receipts'])
            z=cnf_solver(F,n,(),(),10**7)
            assert z['status']==('WITNESS' if W else 'EMPTY')
            if W:assert z['witness'] in W
            C['sources']+=1
    root=ContinuationAllowance(100_000_000)
    for n in range(1,6):
        F=tuple((i+1,) for i in range(n));q=cnf_dispatch(F,n,(),(),root,1000000,solver=cnf_solver);assert q['status']=='WITNESS' and q['witness']==(1,)*n;C['typed_cnf']+=1
    for H,flats,x in product(((),((3,0),),((3,1),)),((),(((1,0),(2,0)),)),range(4)):
        if not satisfies(x,H,flats):continue
        q=hard_dispatch(2,(3,),H,(0,),x,flats,root,3000000,solver=cnf_solver)
        if q['status']=='SAT':assert x==0
        elif q['status']=='MINIMUM':assert x.bit_count()==min(y.bit_count() for y in range(4) if satisfies(y,H,flats))
        else:assert q['status']=='IMPROVED' and satisfies(q['witness'],H,flats) and q['witness'].bit_count()<x.bit_count()
        C[q['status']]+=1
    assert sum(root.charges.values())+root.left==root.total
    print(dict(C),root.charges)
if __name__=='__main__':main()
