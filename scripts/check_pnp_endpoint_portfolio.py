"""Endpoint-facing dispatcher using existing shared reservation owner.
Clipped and exact-one outcomes never infer completion from a refused search.
"""
from check_pnp_endpoint_live_fold import solve,guarded
from check_pnp_clause_syndrome_fold import solve_fold
from check_p0_signed_contrast_20261125 import ContinuationAllowance


def cnf_solver(F,n,rows,target,cap,data_clock=None):
    root=ContinuationAllowance(cap);first=cap//2
    assert root.reserve('live_boundary',first)
    q=solve(F,n,rows,target,(),first,data_clock=data_clock)
    if q['status']!='UNKNOWN':return dict(q,reserved=first,route='live_boundary')
    rest=root.left;assert root.reserve('prior_fold',rest)
    q=solve_fold(F,n,rows,target,rest,data_clock=data_clock)
    return dict(q,reserved=cap,route='prior_fold',first_refused=True)


def singleton_or_relative(F,n,root,cap,relative=False):
    if not root.reserve('relative' if relative else 'singleton',cap):return dict(status='UNKNOWN')
    if relative:return guarded(F,n,cap)
    return solve(F,n,(),(),(),cap,clip=2)


def main():
    from check_pnp_typed_portfolio import cnf_dispatch,hard_dispatch
    from itertools import product
    root=ContinuationAllowance(100_000_000);C={}
    def bump(s):C[s]=C.get(s,0)+1
    for n in range(1,6):
        F=tuple((i+1,) for i in range(n));q=cnf_dispatch(F,n,(),(),root,1000000,solver=cnf_solver)
        assert q['status']=='WITNESS' and q['witness']==(1,)*n;bump('typed_cnf')
        q=singleton_or_relative(F,n,root,1000000);assert q['count']==1 and q['witness']==(1,)*n;bump('singleton')
        for G,expected in ((F,'SAT'),(F+((-1,),),'UNSAT')):
            q=singleton_or_relative(G,n,root,1000000,True);assert q['decision']==expected;bump('guarded')
    for H,flats,x in product(((),((3,0),),((3,1),)),((),(((1,0),(2,0)),)),range(4)):
        from check_pnp_typed_portfolio import satisfies
        if not satisfies(x,H,flats):continue
        q=hard_dispatch(2,(3,),H,(0,),x,flats,root,3000000,solver=cnf_solver)
        if q['status']=='SAT':assert x==0
        elif q['status']=='MINIMUM':assert x.bit_count()==min(y.bit_count() for y in range(4) if satisfies(y,H,flats))
        else:assert q['status']=='IMPROVED' and satisfies(q['witness'],H,flats) and q['witness'].bit_count()<x.bit_count()
        bump(q['status'])
    assert sum(root.charges.values())+root.left==root.total
    assert singleton_or_relative(((1,),),1,root,root.left+1)['status']=='UNKNOWN';bump('refusal')
    assert singleton_or_relative(((1,),),1,root,0,True)['decision']=='UNKNOWN';bump('refusal')
    print(C,root.charges)
if __name__=='__main__':main()
