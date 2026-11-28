"""Bounded local existential projection, with original Boolean patches.
Classical variable elimination; retain boundary and (for affine sources) syndrome.
No assertion that arbitrary inhabited CNF has a bounded separator.
"""
from itertools import product


def canon(F):
    return tuple(sorted({tuple(sorted(set(c))) for c in F if not any(-l in c for l in c)}))


def accepts(F,x):
    return all(any(x[abs(l)-1]==int(l>0) for l in c) for c in F)


def project(F,n,D,cap,width=4,rows=()):
    """Return (receipt or None, charged work). D is forgotten, S retained.
    A table key is (boundary bits, exact F3 contribution of D). Each value
    is (representative patch, number of original interior assignments).
    Reserve all enumeration before it starts. Logical, not physical units.
    """
    if min(n,cap,width)<0:raise ValueError('bounds')
    F=tuple(tuple(c) for c in F);rows=tuple(tuple(r) for r in rows);D=tuple(sorted(set(D)))
    if not D or any(not 0<=i<n for i in D) or any(not 1<=abs(l)<=n for c in F for l in c) or any(len(r)!=n for r in rows):raise ValueError('source')
    scan=1+sum(1+len(c) for c in F)+len(rows)*(n+1)+len(D)
    if scan>cap:return None,0
    I=set(D);H=tuple(c for c in F if any(abs(l)-1 in I for l in c));G=tuple(c for c in F if not any(abs(l)-1 in I for l in c))
    S=tuple(sorted({abs(l)-1 for c in H for l in c}-I))
    if len(D)>width or len(S)>width:return None,scan
    cost=scan+(1<<(len(D)+len(S)))*(scan+len(D)+len(S)+1)
    if cost>cap:return None,scan
    table={}
    for s in product((0,1),repeat=len(S)):
        for d in product((0,1),repeat=len(D)):
            x=dict(zip(S,s));x.update(zip(D,d))
            if not accepts(H,x):continue
            y=tuple(sum(r[i]*b for i,b in zip(D,d))%3 for r in rows)
            key=(s,y);p,k=table.get(key,(d,0));table[key]=(p,k+1)
    # Plain CNF projection is one common residual with exact blockers.
    # With affine rows, retain a syndrome relation rather than erase it.
    blockers=tuple(tuple(-i-1 if b else i+1 for i,b in zip(S,s)) for s in product((0,1),repeat=len(S)) if (s,()) not in table) if not rows else ()
    return dict(D=D,S=S,G=canon(G+blockers),table=table,rows=rows),cost


def reopen(P,x,target=()):
    """Residual membership plus matching syndrome is necessary/sufficient."""
    D,S,G,R=P['D'],P['S'],P['G'],P['rows'];I=set(D)
    if len(R)!=len(target) or not accepts(G,x):return None
    s=tuple(x[i] for i in S);y=tuple((t-sum(a*b for i,(a,b) in enumerate(zip(r,x)) if i not in I))%3 for r,t in zip(R,target))
    entry=P['table'].get((s,y))
    if entry is None:return None
    d,k=entry;p=dict(zip(D,d))
    return tuple(p.get(i,b) for i,b in enumerate(x)),k


def descend(F,n,cap,width=4):
    """Compose exact plain-CNF projections; reverse order reopening."""
    F=tuple(tuple(c) for c in F);G=canon(F);left=cap;patches=[];gone=set()
    while G and () not in G:
        # Deterministic source-derived singleton or clause neighbourhood.
        scan=1+sum(1+len(c) for c in G)+n
        if scan>left:break
        left-=scan
        candidates={(i,) for c in G for i in (abs(l)-1 for l in c)}
        candidates.update(tuple(sorted({abs(l)-1 for l in c})) for c in G if 0<len(c)<=width)
        for D in sorted(candidates,key=lambda d:(len(d),d)):
            assert not gone.intersection(D)
            P,used=project(G,n,D,left,width);left-=used
            if P is None:continue
            patches.append(P);gone.update(D);G=P['G'];break
        else:break
    if () in G:return 'EMPTY',None,G,patches,cap-left
    if not G:
        x=lift(patches,(0,)*n);assert accepts(F,x)
        return 'WITNESS',x,G,patches,cap-left
    return 'UNKNOWN',None,G,patches,cap-left


def lift(patches,x):
    for P in reversed(patches):
        q=reopen(P,x);assert q is not None
        x=q[0]
    return x
