"""Original normal-space witness and punctured-support routes, no GF2/F3 conflation.
Use existing direct-branch sparse one-hot join on original incidence parity chart.
Every attempt reserves its whole logical allowance; failed attempts are not free.
"""
from check_pnp_affine_normal_components import canon,chart,lift,bits,cnf_flats,satisfies,Budget,Exhausted,solve as component_solve
from check_pnp_normal_boundary_join import solve as normal_solve,join_exact_one,value
from check_p0_signed_contrast_20261125 import ContinuationAllowance
from check_pnp_endpoint_portfolio import cnf_solver as prior_solver
from check_pnp_bit_data_schedule import audit,Refused as DataRefused


def normal_probe(F,n,H,root,cap,component=False):
    if n<0 or any(not 1<=abs(l)<=n for c in F for l in c) or any(not 0<=a<1<<n or b not in (0,1) for a,b in H):raise ValueError('original source')
    if not root.reserve('normal_boundary',cap):return dict(status='UNKNOWN',reserved=0)
    # Preflight actual conversion; donor budget is remaining share only.
    setup=1+n+len(H)*(n+1)+sum(1+len(c)*(n+1) for c in F)
    if setup>cap:return dict(status='UNKNOWN',reserved=cap,stop='normal_setup')
    G=cnf_flats(F)
    if component:
        B=Budget(cap-setup);w=None
        try:x=component_solve(n,H,G,B);done=True
        except (Exhausted,RecursionError):x=None;done=False
    else:
        try:x,w,stats,done=normal_solve(n,H,G,cap-setup)
        except RecursionError:x=None;w=None;done=False
    if not done:return dict(status='UNKNOWN',reserved=cap,stop='normal_budget')
    if x is None:return dict(status='EMPTY',reserved=cap,width=w)
    assert satisfies(x,H,G)
    z=tuple(x>>i&1 for i in range(n));assert all(any(z[abs(l)-1]==int(l>0) for l in c) for c in F)
    return dict(status='WITNESS',witness=z,reserved=cap,width=w)


def normal_clipped(F,n,H,root,cap,known=None):
    """Two existential calls, not global counting. Preserve a known witness on refusal."""
    if known is None:
        q=normal_probe(F,n,H,root,cap//2)
        if q['status']=='EMPTY':return dict(q,count=0)
        if q['status']!='WITNESS':return q
        known=q['witness'];cap-=cap//2
    if len(known)!=n or any(b not in (0,1) for b in known):raise ValueError('anchor')
    x=sum(b<<i for i,b in enumerate(known))
    if not satisfies(x,H,cnf_flats(F)):raise ValueError('anchor not satisfying')
    # Original point complement is one original blocking clause, including n=0.
    block=tuple((i+1)*(1-2*b) for i,b in enumerate(known))
    q=normal_probe(F+(block,),n,H,root,cap)
    if q['status']=='UNKNOWN':return dict(q,witness=known,lower=1,upper=2)
    if q['status']=='EMPTY':return dict(status='COMPLETE',count=1,witness=known)
    assert q['witness']!=known
    return dict(status='COMPLETE',count=2,witness=known,other=q['witness'])


def exact_cover(O,n,root,cap):
    if n<0 or any(len(set(c))!=len(c) or any(not 0<=i<n for i in c) for c in O):raise ValueError('incidence')
    if not root.reserve('normal_exact_one',cap):return dict(status='UNKNOWN')
    B=Budget(cap)
    try:
        B.pay('original_chart',1+n+sum(1+len(c)*(n+1) for c in O))
        P=canon((sum(1<<i for i in c),1) for c in O)
        if P is None:return dict(status='EMPTY',route='parity_inconsistent')
        u,V=chart(n,P);G=tuple(tuple((value(V,1<<i),u>>i&1) for i in c) for c in O)
        y,w=join_exact_one(len(V),G,B)
        if y is None:return dict(status='EMPTY',width=w,route='normal_exact_one')
        x=lift(u,V,y);z=tuple(x>>i&1 for i in range(n))
        B.pay('original_verify',1+n+sum(1+len(c) for c in O))
        assert all(sum(z[i] for i in c)==1 for c in O)
        return dict(status='WITNESS',witness=z,width=w,route='normal_exact_one')
    except Exhausted:return dict(status='UNKNOWN',route='normal_exact_one')


def cnf_solver(F,n,rows,target,cap,data_clock=None):
    # F3 equations cannot be reinterpreted as GF2. Keep existing typed path.
    if rows or target:return prior_solver(F,n,rows,target,cap,data_clock)
    root=ContinuationAllowance(cap);a=cap//2
    q=normal_probe(F,n,(),root,a,component=True)
    if q['status']=='UNKNOWN':
        rest=root.left;assert root.reserve('previous',rest)
        return dict(prior_solver(F,n,rows,target,rest,data_clock),reserved=cap,component_refused=True)
    else:
        q=dict(q,reserved=a,route='normal_component')
    if q['status']=='WITNESS' and data_clock is not None:
        try:assert audit(F,(),(),q['witness'],data_clock)
        except DataRefused:q['status']='WITNESS_DATA_AUDIT_REFUSED'
    return q
