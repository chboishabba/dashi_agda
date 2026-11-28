"""Opt-in original CNF route with separately reserved separator replay."""
from check_pnp_source_derived_cover import Reservation,Refused
from check_pnp_prime_power_incidence import exact_rows,incidence
from check_pnp_boolean_separator import fold,replay
from check_pnp_integer_fibre_portfolio import cnf_solver as prior
from check_p0_signed_contrast_20261125 import ContinuationAllowance
from check_pnp_frontier_resolution import accepts,norm


def separator_source(F,n,cap,max_width=12,clip=2):
    B=Reservation(cap)
    try:
        O=exact_rows(F,n,B);B.pay(1+len(O)*(n+1));A,b=incidence(O,n)
    except Refused:return dict(status='UNKNOWN',reserved=cap-B.left)
    # Distinct budgets; replay must finish to promote EMPTY or a count.
    first=B.left//2;B.pay(first);q=fold(A,b,n,F=F,cap=first,max_width=max_width,clip=clip)
    if q['status']=='UNKNOWN':return dict(q,reserved=cap-B.left,route='separator_refused')
    rest=B.left;B.pay(rest)
    if not replay(A,b,n,F,(),(),(),q,rest,clip=clip):return dict(status='UNKNOWN',reserved=cap,route='replay_refused')
    return dict(q,reserved=cap,route='separator_replayed')


def cnf_solver(F,n,rows,target,cap,data_clock=None):
    if rows or target or data_clock is not None:return prior(F,n,rows,target,cap,data_clock)
    root=ContinuationAllowance(cap);a=cap//2;assert root.reserve('separator',a)
    q=separator_source(F,n,a)
    if q['status']!='UNKNOWN':return dict(q,reserved=a)
    rest=root.left;assert root.reserve('prior',rest)
    return dict(prior(F,n,rows,target,rest,data_clock),reserved=cap,route='prior_after_separator')


def guarded(F,n,cap):
    from check_pnp_guarded_resolution_boundary import guarded as make,restrict_clause
    B=Reservation(cap)
    try:B.pay(1+3*n+sum(2+len(c) for c in F))
    except Refused:return dict(status='UNKNOWN',reserved=cap-B.left)
    H,G=make(F,n);anchor=(0,)*(n+1);assert accepts(H,anchor)
    R=tuple(r for c in G if (r:=restrict_clause(c,{n:1})) is not None);assert R==tuple(map(norm,F))
    q=cnf_solver(R,n,(),(),B.left);used=cap-B.left+q['reserved']
    if q['status']=='EMPTY':return dict(status='COMPLETE',count=1,witness=anchor,reserved=used,route=q['route'])
    if q['status']=='WITNESS':
        x=q['witness']+(1,);assert accepts(G,x);return dict(status='COMPLETE',count=2,witness=anchor,other=x,reserved=used,route=q['route'])
    return dict(status='UNKNOWN',witness=anchor,lower=1,upper=2,reserved=used)


def main():
    from random import Random
    from itertools import product,combinations
    from collections import Counter
    rng=Random(3693502);C=Counter()
    for n in range(1,9):
        for _ in range(24):
            O=tuple(tuple(i for i in range(n) if rng.randrange(2)) for j in range(rng.randrange(4)))
            F=tuple(tuple(i+1 for i in c) for c in O)+tuple((-i-1,-j-1) for c in O for i,j in combinations(c,2))
            F+=tuple(tuple(rng.choice((-1,1))*rng.randrange(1,n+1) for j in range(3)) for i in range(2))
            W=[x for x in product((0,1),repeat=n) if accepts(F,x)];q=cnf_solver(F,n,(),(),10**7);assert q['status']==('WITNESS' if W else 'EMPTY')
            g=guarded(F,n,10**7);assert g['count']==(2 if W else 1)
            if W:assert q['witness'] in W and g['other'][:-1] in W
            C[q['route']]+=1
    for k in (16,32,64):
        F=tuple((i,i+1) for i in range(1,k));q=separator_source(F,k,10**7);assert q['status']=='WITNESS' and q['count']==2
        old=prior(F,k,(),(),10**7);assert old['status'] in ('WITNESS','UNKNOWN')
        print('connected',k,q['points'],q['used'],old['status'])
    assert guarded(((1,),),1,0)['status']=='UNKNOWN'
    print(dict(C),'guarded 192, refusal PASS')
if __name__=='__main__':main()
