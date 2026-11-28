"""One bounded original-source mass screen, reused for every Toeplitz scale.
An unresolved screen is never UNSAT; low potential is not an impossible witness.
"""
from fractions import Fraction as Q
from math import ceil,floor
from check_p0_signed_contrast_20261125 import canon,cell,refine,ContinuationAllowance
from check_pnp_constructive_descent import search

def potential(m,D):return Q(m*(D+1-m),D*D)

def potential_bounds(l,u,D):
    if not 0<=l<=u or D<1:raise ValueError('mass interval')
    a,b=potential(l,D),potential(u,D)
    v=max(l,min(u,(D+1)//2))
    return min(a,b),max(a,b,potential(v,D))

def screen(F,n,cap,split_budget=0):
    F=tuple(tuple(c) for c in F)
    if min(n,cap,split_budget)<0 or any(not 1<=abs(l)<=n for c in F for l in c):raise ValueError('source')
    F=canon(F);ledger=ContinuationAllowance(cap)
    cols=((0,),)*n
    root=cell(F,cols,(),0,tuple(range(n)),Q(1),ledger=ledger)
    if root is None:l=u=0;splits=0
    else:
        # No contrast can meet this deliberately impossible threshold.
        # Refine to the charged cap or exact closure, not first positive sign.
        lo,hi,_,splits=refine([root],-Q((1<<(n+1))+1),split_budget,exact_probe_budget=cap,ledger=ledger)
        l=max(0,ceil(-hi[2]));u=min(1<<n,floor(-lo[2]))
    rows=[]
    for k in range(1,n+2):
        D=3**k;a,b=potential_bounds(l,u,D)
        status='promised' if a>Q(1,12) else 'below' if b<=Q(1,12) else 'unresolved'
        rows.append(dict(k=k,lo=str(a),hi=str(b),status=status))
    order=sorted(rows,key=lambda a:({'promised':0,'unresolved':1,'below':2}[a['status']],-Q(a['lo']),-Q(a['hi']),a['k']))
    return dict(mass=(l,u),reserved=cap-ledger.left,charges=dict(ledger.charges),baseline_cells=ledger.baseline_cells,splits=splits,scales=rows,order=[a['k'] for a in order])

def screened_search(F,n,cap,screen_cap=4096,split_budget=4,exact_probe_budget=0,keep_low=True):
    """Reserve screening once and split the remaining allowance over chosen scales."""
    if min(cap,screen_cap)<0:raise ValueError('cap')
    F=tuple(tuple(c) for c in F);screen_cap=min(cap,screen_cap);s=screen(F,n,screen_cap)
    below={r['k'] for r in s['scales'] if r['status']=='below'}
    order=[k for k in s['order'] if keep_low or k not in below]
    if s['mass'][1]==0 or not order:return None,s,[]
    per=(cap-screen_cap)//len(order)
    x,rec=search(F,n,per,split_budget,exact_probe_budget,scales=order)
    assert screen_cap+sum(a['reserved'] for a in rec)<=cap
    s.update(screen_allocated=screen_cap,per_scale=per,selected=order)
    return x,s,rec
