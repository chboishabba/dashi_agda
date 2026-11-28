"""Original source attachment. Smith is an offline diagnostic, not paid fallback."""
from itertools import combinations,product
from check_pnp_source_derived_cover import Reservation,Refused
from check_pnp_prime_power_incidence import exact_rows,incidence,latin
from check_pnp_boolean_fibre import solve as fibre
from check_pnp_smith_certificate import solve as smith
from check_pnp_hall_geometry import cnf_solver as prior
from check_pnp_frontier_resolution import accepts
from check_p0_signed_contrast_20261125 import ContinuationAllowance


def chart_source(F,n,cap,max_width=12):
    B=Reservation(cap)
    try:
        O=exact_rows(F,n,B);B.pay(1+len(O)*(n+1));A,b=incidence(O,n)
    except Refused:return dict(status='UNKNOWN',reserved=cap-B.left)
    q=fibre(A,b,n,F=F,cap=B.left,max_width=max_width)
    if q['status']=='WITNESS':assert accepts(F,q['witness'])
    return dict(q,reserved=cap-B.left+q['used'],rows=O)


def cnf_solver(F,n,rows,target,cap,data_clock=None):
    if rows or target or data_clock is not None:return prior(F,n,rows,target,cap,data_clock)
    root=ContinuationAllowance(cap);first=cap//4;assert root.reserve('boolean_fibre',first)
    q=chart_source(F,n,first)
    if q['status']!='UNKNOWN':return dict(q,reserved=first,route='boolean_fibre')
    rest=root.left;assert root.reserve('prior',rest)
    return dict(prior(F,n,rows,target,rest,data_clock),reserved=cap,route='prior_after_fibre')


def smith_source(F,n,admission=4096):
    # Explicit admission, not execution cost. No Smith result is promoted
    # to Boolean feasibility; integer inconsistency may certify EMPTY.
    O=exact_rows(F,n,Reservation(10**7));A,b=incidence(O,n);q=smith(A,b,n,max_entries=admission)
    return dict(q,rows=O,route='offline_smith')


def guarded(F,n,cap):
    from check_pnp_guarded_resolution_boundary import guarded as make,restrict_clause
    from check_pnp_frontier_resolution import norm
    B=Reservation(cap)
    try:B.pay(1+3*n+sum(2+len(c) for c in F))
    except Refused:return dict(status='UNKNOWN')
    H,G=make(F,n);a=(0,)*(n+1);assert accepts(H,a)
    R=tuple(r for c in G if (r:=restrict_clause(c,{n:1})) is not None);assert R==tuple(map(norm,F))
    q=cnf_solver(R,n,(),(),B.left)
    if q['status']=='EMPTY':return dict(status='COMPLETE',count=1,witness=a)
    if q['status']=='WITNESS':
        x=q['witness']+(1,);assert accepts(G,x);return dict(status='COMPLETE',count=2,witness=a,other=x)
    return dict(status='UNKNOWN',witness=a,lower=1,upper=2)


def main():
    from random import Random
    rng=Random(3693403);C={}
    for n in range(1,9):
        for _ in range(24):
            O=tuple(tuple(i for i in range(n) if rng.randrange(2)) for j in range(rng.randrange(4)))
            F=tuple(tuple(i+1 for i in c) for c in O)+tuple((-i-1,-j-1) for c in O for i,j in combinations(c,2))
            F+=tuple(tuple(rng.choice((-1,1))*rng.randrange(1,n+1) for j in range(3)) for i in range(2))
            W=[x for x in product((0,1),repeat=n) if accepts(F,x)];q=cnf_solver(F,n,(),(),10**7);assert q['status']==('WITNESS' if W else 'EMPTY')
            g=guarded(F,n,10**7);assert g['count']==(2 if W else 1)
            if W:assert q['witness'] in W and g['other'][:-1] in W
            s=smith_source(F,n);assert not W or s['status']=='INTEGER'
            C[q['route']]=C.get(q['route'],0)+1
    for k in (2,4,8):
        T,O=latin(k);F=tuple(tuple(i+1 for i in c) for c in O)+tuple((-i-1,-j-1) for c in O for i,j in combinations(c,2));s=smith_source(F,len(T),admission=10000);assert s['status']=='EMPTY'
    # Components of growing but small width, exact cross-source mass.
    for w in (2,4,8,12):
        k=4;n=k*w;F=tuple(c for i in range(k) for j in range(i*w,i*w+w-1) for c in ((-j-1,j+2),(j+1,-j-2)))
        q=fibre((),(),n,F=F,cap=10**8,max_width=w);assert q['count']==2**k and q['width']==w and q['points']==k*2**w
        print('components',w,n,q['points'],q['used'])
    assert guarded(((1,),),1,0)['status']=='UNKNOWN'
    print(C,'192 guarded controls, 3 Smith incidence controls, refusal PASS')
if __name__=='__main__':main()
