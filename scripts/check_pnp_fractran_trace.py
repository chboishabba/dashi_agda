"""Witness-to-trace adapter; no endpoint search or unrestricted contraction claim."""
from check_pnp_affine_normal_components import bits, canon, chart, satisfies

def trace(n,R,H,caps,x,y,B,flats=()):
    """Return signed macro receipt, or None on nonimprovement/prefix refusal.
    Budget exceptions propagate; caller must retain original state.
    Hard nonlinear flats are checked at macro boundaries, not microstates.
    """
    R,H,caps,flats=tuple(R),tuple(H),tuple(caps),tuple(flats)
    B.pay('trace_input',1+n*(1+len(H)+len(R)+sum(map(len,flats))))
    if len(R)!=len(caps) or any(r<0 or r>>n for r in R) or any(c<0 for c in caps):
        raise ValueError('invalid capacity source')
    if any(a<0 or a>>n or b not in (0,1) for a,b in H) or any(a<0 or a>>n or b not in (0,1) for F in flats for a,b in F):
        raise ValueError('invalid demand')
    if any(z<0 or z>>n for z in (x,y)) or not all(satisfies(z,H,flats) for z in (x,y)):
        raise ValueError('endpoint outside demand')
    Q=canon(H)
    if Q is None: raise ValueError('inconsistent demand')
    u,V=chart(n,Q)
    piv={a.bit_length()-1 for a,b in Q}
    free=[i for i in range(n) if i not in piv]
    residual=lambda z: tuple((r&z).bit_count()-c for r,c in zip(R,caps))
    potential=lambda r:sum(max(0,a) for a in r)
    initial=residual(x);target=residual(y)
    if potential(target)>=potential(initial):return None
    state=x;rr=initial;out=[]
    for j,v in zip(free,V):
        if not ((x^y)>>j&1):continue
        B.pay('trace_macro',1+n*(1+len(H)+len(R)+sum(map(len,flats))))
        nxt=state^v
        if not satisfies(nxt,H,flats):return None
        signed=tuple((i,1-2*((state>>i)&1)) for i in bits(v))
        micro=state;cur=list(rr);units=[]
        for i,d in signed:
            B.pay('trace_unit',1+n+len(R))
            # One-hot Boolean prime tags (coordinate, sign): symbolic
            # numerator/denominator, not expanded integers or runtime claims.
            before=(micro>>i)&1
            if d!=1-2*before:raise AssertionError('orientation')
            micro^=1<<i
            dr=tuple(d*((r>>i)&1) for r in R)
            cur=[a+b for a,b in zip(cur,dr)]
            if tuple(cur)!=residual(micro):raise AssertionError('residual')
            units.append(dict(coord=i,delta=d,denominator=(i,before),
                              numerator=(i,1-before),state=micro,
                              delta_residual=dr,residual=tuple(cur)))
        if micro!=nxt or tuple(cur)!=residual(nxt):raise AssertionError('decode')
        out.append(dict(before=state,after=nxt,basis=v,units=units,
                        residual=tuple(cur),potential=potential(cur)))
        state=nxt;rr=tuple(cur)
    if state!=y or rr!=target:raise AssertionError('endpoint')
    return dict(start=x,end=y,demand=H,hard_flats=flats,rows=R,caps=caps,
                initial=initial,final=target,macros=out,
                decrease=potential(initial)-potential(target))

def recover_trace(n,R,H,caps,x,B,signed_screen=False,flats=()):
    """Existing consumer owns discovery; receipt is optional and transactional."""
    from check_pnp_capacity_partition import recover_cell
    from check_pnp_demand_strata import ProbeLimit
    from check_pnp_affine_normal_components import Exhausted
    Q=canon(H)
    if Q is None or not satisfies(x,H,flats):raise ValueError('invalid start')
    try:
        v=recover_cell(n,R,Q,caps,B,signed_screen=signed_screen)
        if v.witness is None:return None
        if not satisfies(v.witness,H,flats):return None
        return trace(n,R,H,caps,x,v.witness,B,flats)
    except (ProbeLimit,Exhausted,RecursionError):return None
