"""Bounded component reopening on row-support spans, not XOR graph appearance."""
from check_pnp_affine_normal_components import bits, split, reopen, chart, satisfies
from check_pnp_signed_capacity_square import row_ledger


def evaluate(M,z):
    return sum(-c if (a&z).bit_count()%2 else c for a,c in M.items())


def components(d,M,caps,B,width=8):
    """(status, chart witness, component widths). Width refusal is UNKNOWN.
    Synthetic zero equations are used ONLY to discover support incidence;
    they are not new constraints imposed on original feasible points.
    """
    assert len(M)==len(caps)
    F=[]
    for m,c in zip(M,caps):
        B.pay('ledger_component_support',1+len(m))
        A=tuple((a,0) for a in sorted(m) if a)
        if A:F.append(A)
        elif m.get(0,0)>2*c:return 'empty',None,()
    basis,parts=split(d,F,B);k=len(basis)
    B.pay('ledger_component_dual',1+(1+d)*(1+k)**3)
    dual=[reopen(d,basis,1<<i) for i in range(k)]
    def coord(a):
        q=sum(((a&v).bit_count()%2)<<i for i,v in enumerate(dual));r=0
        for i in bits(q):r^=basis[i]
        assert r==a
        return q
    blocks=[tuple(I) for I,_ in parts];masks=[sum(1<<i for i in I) for I in blocks];local=[[] for _ in blocks]
    for m,c in zip(M,caps):
        B.pay('ledger_component_coordinates',1+(1+k)*len(m));Q={coord(a):v for a,v in m.items()};scope=0
        for q in Q:scope|=q
        if not scope:continue
        ids=[j for j,mask in enumerate(masks) if scope&mask];assert len(ids)==1
        j=ids[0];I=blocks[j];local[j].append(({sum(((q>>i)&1)<<t for t,i in enumerate(I)):v for q,v in Q.items()},c))
    widths=tuple(map(len,blocks));z=0;unknown=False
    for I,rows in zip(blocks,local):
        if len(I)>width:unknown=True;continue
        B.pay('ledger_component_scan',(1<<len(I))*(1+sum(len(m) for m,c in rows)))
        y=next((x for x in range(1<<len(I)) if all(evaluate(m,x)<=2*c for m,c in rows)),None)
        if y is None:return 'empty',None,widths
        z|=sum(((y>>j)&1)<<i for j,i in enumerate(I))
    if unknown:return 'unknown',None,widths
    B.pay('ledger_component_reopen',1+(1+d)*(1+k)**2+sum(len(m) for m in M));y=reopen(d,basis,z)
    assert all(evaluate(m,y)<=2*c for m,c in zip(M,caps))
    return 'witness',y,widths


def recover(n,R,H,caps,B,width=8):
    B.pay('ledger_component_chart',1+(1+n)*(1+len(H))+sum(r.bit_count() for r in R)*(1+n-len(H)))
    u,V=chart(n,H);M=[row_ledger(r,u,V) for r in R]
    status,y,widths=components(len(V),M,caps,B,width)
    if y is None:return status,None,widths
    x=u
    for i in bits(y):x^=V[i]
    B.pay('ledger_component_verify',1+n+sum(r.bit_count() for r in R))
    assert satisfies(x,H,()) and all((r&x).bit_count()<=c for r,c in zip(R,caps))
    return status,x,widths


def screen(n,R,H,caps,B):
    """Compose the new observer with the existing bounded component reopening."""
    from check_pnp_signed_capacity_rank2 import screen as contract
    from check_pnp_affine_normal_components import Exhausted
    from check_pnp_demand_strata import ProbeLimit
    Q,y,reason=contract(n,R,H,caps,B)
    if Q is None or y is not None:return Q,y,reason
    try:status,x,widths=recover(n,R,Q,caps,B)
    except (ProbeLimit,Exhausted):return Q,None,'component_refused'
    if status=='empty':return None,None,'component_empty'
    if status=='witness':return Q,x,'component_witness'
    return Q,None,'component_width_refused'
