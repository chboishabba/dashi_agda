"""Source-derived disjoint interiors on a fixed original exterior.
Logical cap only; no universal width or physical time assertion.
"""
from check_pnp_conditional_autarky import accepts, project
from check_pnp_hyperfabric_epoch_cluster_abi import cluster_join


def planned_cluster_join(F, n, exterior, x, rows, target, cap, width=4):
    """Return (count, original representative, charged work), or None.
    Refusal is not EMPTY. Every candidate construction uses one cap.
    The exterior indices and values are explicit, not discovered for free.
    """
    if min(n, cap, width) < 0:
        raise ValueError('bounds')
    F=tuple(tuple(c) for c in F); rows=tuple(tuple(r) for r in rows)
    E=set(exterior); x=tuple(x); target=tuple(target)
    if len(x)!=n or any(b not in (0,1) for b in x) or any(i<0 or i>=n for i in E):
        raise ValueError('exterior')
    if len(rows)!=len(target) or any(len(r)!=n for r in rows) or any(not 1<=abs(l)<=n for c in F for l in c):
        raise ValueError('source')
    # Reserve an explicit conservative planning bound before graph construction.
    scan=1+(n+1)**2+sum((1+len(c))**2 for c in F)+len(rows)*(n+1)
    if scan>cap: return None
    left=cap-scan
    D=set(range(n))-E; adj={i:set() for i in D}; untouched=[]
    for c in F:
        V={abs(l)-1 for l in c}&D
        if not V: untouched.append(c)
        for i in V: adj[i].update(V-{i})
    if not accepts(untouched,x): return 0,None,scan
    components=[]; unseen=set(D)
    while unseen:
        start=min(unseen); todo=[start]; unseen.remove(start); C={start}
        while todo:
            i=todo.pop()
            for j in adj[i]&unseen:
                unseen.remove(j); C.add(j); todo.append(j)
        components.append(tuple(sorted(C)))
    patches=[]
    for C in components:
        P,used=project(F,n,C,left,width,rows=rows)
        if P is None: return None
        left-=used
        if not set(P['S'])<=E: raise RuntimeError('invalid source component')
        patches.append(P)
    out=cluster_join(patches,x,rows,target,left)
    if out is None: return None
    count,witness,used=out
    left-=used
    # Pay a separate original-source witness validation, even if count is zero.
    audit=1+n+sum(1+len(c) for c in F)+len(rows)*(n+1)
    if audit>left: return None
    left-=audit
    if count:
        if witness is None or any(witness[i]!=x[i] for i in E) or not accepts(F,witness):
            raise RuntimeError('invalid original lift')
        if tuple(sum(a*b for a,b in zip(r,witness))%3 for r in rows)!=tuple(t%3 for t in target):
            raise RuntimeError('invalid original syndrome')
    elif witness is not None: raise RuntimeError('zero count with witness')
    return count,witness,cap-left
