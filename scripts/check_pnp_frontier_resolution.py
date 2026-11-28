"""Bounded original CNF conflict learning, with replayable resolution DAG.
No singleton promise used to justify an inference. UNKNOWN retains sound lemmas.
"""
from check_pnp_source_derived_cover import Reservation, Refused
from check_p0_signed_contrast_20261125 import ContinuationAllowance
from check_pnp_endpoint_live_fold import solve as live
from check_pnp_normal_endpoint_weld import cnf_solver as prior


def norm(c):return tuple(sorted(set(c)))
def accepts(F,x):return all(any(x[abs(l)-1]==int(l>0) for l in c) for c in F)
def resolvent(a,b,p):
    if p not in a or -p not in b:raise ValueError('pivot')
    return norm((set(a)-{p})|(set(b)-{-p}))


def replay(F,n,proof,B):
    """Independent check of each named original or earlier resolution clause."""
    D=[]
    for c in F:
        B.pay(1+len(c));D.append(norm(c))
    for i,j,p,c in proof:
        B.pay(1+len(c))
        if not (0<=i<len(D) and 0<=j<len(D) and 1<=abs(p)<=n):return None
        B.pay(len(D[i])+len(D[j]))
        try:r=resolvent(D[i],D[j],p)
        except ValueError:return None
        if r!=c:return None
        D.append(c)
    return tuple(D)


def learn(F,n,cap):
    if n<0 or any(not 1<=abs(l)<=n for c in F for l in c):raise ValueError('source')
    B=Reservation(cap);C=[];ix={};proof=[];nodes=0;conflicts=0
    def add(a,b,p):
        B.pay(1+len(C[a])+len(C[b]));c=resolvent(C[a],C[b],p)
        if c in ix:return ix[c]
        B.pay(1+len(c));j=len(C);C.append(c);ix[c]=j;proof.append((a,b,p,c));return j
    def conflict(j,trail,reason):
        nonlocal conflicts
        conflicts+=1
        # Eliminate implied variables in reverse trail order. Remaining
        # clause is falsified by decision coordinates only.
        for v in reversed(trail):
            p=trail[v];r=reason[v]
            B.pay(1+len(C[j]))
            if r is not None and -p in C[j]:j=add(j,r,-p)
        assert all(abs(l) in trail and trail[abs(l)]==-l and reason[abs(l)] is None for l in C[j])
        return j
    def rec(trail,reason):
        nonlocal nodes
        B.pay(1+n);nodes+=1
        # Propagate original and globally entailed learned clauses.
        while True:
            changed=False;unresolved=[]
            for j,c in enumerate(C):
                B.pay(1+len(c))
                if any(trail.get(abs(l))==l for l in c):continue
                u=tuple(l for l in c if abs(l) not in trail)
                if not u:return None,conflict(j,trail,reason)
                if len(u)==1:
                    p=u[0];trail[abs(p)]=p;reason[abs(p)]=j;changed=True;break
                unresolved.extend(map(abs,u))
            if not changed:break
        if not unresolved:return tuple(int(trail.get(i,-i)>0) for i in range(1,n+1)),None
        # Most frequent active coordinate, deterministic ties; no oracle.
        B.pay(1+len(unresolved)+n)
        from collections import Counter
        v=max(Counter(unresolved).items(),key=lambda z:(z[1],-z[0]))[0]
        x,a=rec(trail|{v:v},reason|{v:None})
        if x is not None:return x,None
        if -v not in C[a]:return None,a
        x,b=rec(trail|{v:-v},reason|{v:None})
        if x is not None:return x,None
        if v not in C[b]:return None,b
        return None,add(a,b,-v)
    try:
        B.pay(1+n+sum(1+len(c) for c in F));C.extend(map(norm,F))
        ix.update((c,j) for j,c in enumerate(C))
        x,j=rec({},{});status='WITNESS' if x is not None else 'EMPTY'
        if x is not None:
            B.pay(1+n+sum(1+len(c) for c in F));assert accepts(F,x)
        else:assert C[j]==()
        return dict(status=status,witness=x,empty_id=j,proof=tuple(proof),used=cap-B.left,nodes=nodes,conflicts=conflicts)
    except (Refused,RecursionError):
        return dict(status='UNKNOWN',proof=tuple(proof),used=cap-B.left,nodes=nodes,conflicts=conflicts)


def puncture(F,n,anchor,cap):
    if len(anchor)!=n or any(b not in (0,1) for b in anchor) or not accepts(F,anchor):raise ValueError('anchor')
    B=Reservation(cap)
    try:B.pay(1+n+sum(1+len(c) for c in F))
    except Refused:return dict(status='UNKNOWN',witness=anchor,lower=1,upper=2)
    G=F+(tuple((i+1)*(1-2*b) for i,b in enumerate(anchor)),)
    q=learn(G,n,B.left//2);B.pay(q['used'])
    try:D=replay(G,n,q['proof'],B)
    except Refused:return dict(status='UNKNOWN',witness=anchor,lower=1,upper=2)
    assert D is not None
    if q['status']=='EMPTY':
        assert D[q['empty_id']]==()
        return dict(status='COMPLETE',count=1,witness=anchor,used=cap-B.left,proof=q['proof'])
    if q['status']=='WITNESS':
        assert q['witness']!=anchor and accepts(G,q['witness'])
        return dict(status='COMPLETE',count=2,witness=anchor,other=q['witness'],used=cap-B.left)
    # Learned clauses are globally entailed by the actual punctured source.
    # They may improve propagation in the next producer, but can increase width.
    q2=live(D,n,(),(),(),B.left,clip=2)
    if q2['status']=='EMPTY':return dict(status='COMPLETE',count=1,witness=anchor,used=cap-B.left+q2['reserved'],proof=q['proof'])
    if q2['status']=='WITNESS':return dict(status='COMPLETE',count=2,witness=anchor,other=q2['witness'],used=cap-B.left+q2['reserved'])
    return dict(status='UNKNOWN',witness=anchor,lower=1,upper=2,used=cap-B.left+q2['reserved'])


def cnf_solver(F,n,rows,target,cap,data_clock=None):
    # No F3 equation is removed by CNF resolution. Keep typed prior path.
    if rows or target or data_clock is not None:return prior(F,n,rows,target,cap,data_clock)
    root=ContinuationAllowance(cap);a=cap//2;assert root.reserve('resolution',a)
    q=learn(F,n,a//2);B=Reservation(a-q['used'])
    try:D=replay(F,n,q['proof'],B)
    except Refused:D=None
    if D is not None:
        if q['status']=='EMPTY' and D[q['empty_id']]==():return dict(status='EMPTY',reserved=a,route='resolution',proof=q['proof'])
        if q['status']=='WITNESS':return dict(q,reserved=a,route='resolution')
    rest=root.left;assert root.reserve('prior',rest)
    # Never require the fallback to ingest extra clauses merely because
    # they are sound: additional live factors can make its geometry worse.
    return dict(prior(F,n,rows,target,rest,data_clock),reserved=cap,route='prior_after_resolution')
