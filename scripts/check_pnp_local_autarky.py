"""Original CNF local autarkies: exact satisfiability-preserving BIDI reopening.
A bounded neighborhood is not a global witness certificate unless every
clause touched by the patch is satisfied by the patch itself.
"""
from itertools import product
from check_p0_signed_contrast_20261125 import canon,accepts

def patch_for(F,i,cap,width=4):
    if cap<0 or width<1:raise ValueError('bounds')
    # Charge the full source scan before looking at its neighborhoods.
    scan=1+sum(1+len(c) for c in F)
    if scan>cap:return None,0
    used=scan
    touch=[c for c in F if any(abs(l)==i+1 for l in c)]
    candidates={(i,)}
    for c in touch:
        V=tuple(sorted({abs(l)-1 for l in c}))
        if len(V)<=width:candidates.add(V)
    V=tuple(sorted({i}|{abs(l)-1 for c in touch for l in c}))
    if len(V)<=width:candidates.add(V)
    for V in sorted(candidates,key=lambda v:(len(v),v)):
        # No uncharged candidate evaluation; includes construction of touched clauses.
        cost=scan+(1<<len(V))*(scan+len(V)+1)
        if used+cost>cap:continue
        used+=cost;I=set(V);H=[c for c in F if any(abs(l)-1 in I for l in c)]
        for bits in product((0,1),repeat=len(V)):
            p=dict(zip(V,bits))
            if all(any(abs(l)-1 in p and p[abs(l)-1]==int(l>0) for l in c) for c in H):
                return tuple(zip(V,bits)),used
    return None,used

def restrict_patch(F,p):
    p=dict(p)
    assert all(any(abs(l)-1 in p and p[abs(l)-1]==int(l>0) for l in c) for c in F if any(abs(l)-1 in p for l in c))
    return tuple(c for c in F if not any(abs(l)-1 in p for l in c))

def descend(F,n,cap,width=4):
    """Return original verified witness, exact empty, or a residual and reopening patch."""
    F=tuple(tuple(c) for c in F)
    if min(n,cap)<0 or any(not 1<=abs(l)<=n for c in F for l in c):raise ValueError('source')
    G=canon(F);p={};left=cap;receipts=[]
    while G and () not in G:
        for i in range(n):
            if i in p:continue
            q,used=patch_for(G,i,left,width);left-=used
            if q is None:continue
            assert not set(p)&{j for j,b in q}
            G=restrict_patch(G,q);p.update(q);receipts.append(dict(patch=q,used=used))
            break
        else:break
    if () in G:return 'EMPTY',None,G,p,cap-left,receipts
    if not G:
        x=tuple(p.get(i,0) for i in range(n));assert accepts(F,x)
        return 'WITNESS',x,G,p,cap-left,receipts
    return 'UNKNOWN',None,G,p,cap-left,receipts

def reopen(F,n,p,x):
    assert len(x)==n
    y=tuple(p.get(i,x[i]) for i in range(n));assert accepts(F,y)
    return y
