"""Systematic F3 image coordinates + capped exact local Boolean fibre DP.
Reuse the existing RREF owner. All labels count original Boolean lifts.
No complete width/rank guarantee for arbitrary CNF.
"""
from itertools import product
from check_pnp_signed_component_histogram import rref
from check_pnp_conditional_autarky import canon,accepts

class Image:
    def __init__(self,rows,D):
        self.m=len(rows)
        B,self.piv=rref(tuple(tuple(r[i]%3 for r in rows)+(0,) for i in D),self.m)
        self.B=tuple(r[:-1] for r in B)
    def key(self,y):return tuple(y[i]%3 for i in self.piv)
    def decode(self,k):
        return tuple(sum(a*r[i] for a,r in zip(k,self.B))%3 for i in range(self.m))
    def encode(self,y):
        if len(y)!=self.m:raise ValueError('ambient')
        k=self.key(y)
        return k if self.decode(k)==tuple(a%3 for a in y) else None

def project(F,n,D,cap,rows=(),boundary_width=4,interior_width=24):
    F=tuple(tuple(c) for c in F);rows=tuple(tuple(r) for r in rows);D=tuple(sorted(set(D)))
    if min(n,cap,boundary_width,interior_width)<0 or not D or any(not 0<=i<n for i in D) or any(not 1<=abs(l)<=n for c in F for l in c) or any(len(r)!=n for r in rows):raise ValueError('source')
    I=set(D);m=len(rows);work=0
    def pay(k):
        nonlocal work
        if work+k>cap:return False
        work+=k;return True
    scan=1+n+sum(1+len(c) for c in F)+m*(n+1)
    if not pay(scan):return None,work
    H=tuple(c for c in F if any(abs(l)-1 in I for l in c));G=tuple(c for c in F if not any(abs(l)-1 in I for l in c))
    S=tuple(sorted({abs(l)-1 for c in H for l in c}-I))
    if len(D)>interior_width or len(S)>boundary_width:return None,work
    # Conservative field-operation charge for the donor RREF of columns.
    if not pay(1+(m+1)**2*(len(D)+1)**2):return None,work
    image=Image(rows,D);r=len(image.piv);cols=[image.key(tuple(row[i] for row in rows)) for i in D]
    if not pay(1+len(D)*(len(H)+1)*(scan+1)):return None,work
    masks=[tuple(sum(1<<j for j,c in enumerate(H) if (i+1 if b else -i-1) in c) for b in (0,1)) for i in D]
    full=(1<<len(H))-1;table={};peak=0;probes=0
    for s in product((0,1),repeat=len(S)):
        if not pay(scan):return None,work
        pins=dict(zip(S,s));u=sum(1<<j for j,c in enumerate(H) if not any(abs(l)-1 in pins and pins[abs(l)-1]==int(l>0) for l in c))
        states={((0,)*r,u):(0,1)}
        # A failed clause can be discarded as soon as its final variable leaves.
        future=[0]*(len(D)+1)
        for i in range(len(D)-1,-1,-1):future[i]=future[i+1]|masks[i][0]|masks[i][1]
        for i,(c,ms) in enumerate(zip(cols,masks)):
            if not pay(2*len(states)*(r+len(H)+len(D)+2)):return None,work
            nxt={}
            for (k,u),(p,count) in states.items():
                for b in (0,1):
                    probes+=1;v=u&~ms[b]
                    if v&~future[i+1]:continue
                    key=(tuple((a+b*t)%3 for a,t in zip(k,c)),v)
                    q,N=nxt.get(key,(p|(b<<i),0));nxt[key]=(q,N+count)
            states=nxt;peak=max(peak,len(states))
        for (k,u),(p,N) in states.items():
            assert u==0;table[s,k]=(tuple((p>>i)&1 for i in range(len(D))),N)
    blockers=tuple(tuple(-i-1 if b else i+1 for i,b in zip(S,s)) for s in product((0,1),repeat=len(S)) if (s,()) not in table) if not rows else ()
    return dict(D=D,S=S,G=canon(G+blockers),rows=rows,image=image,table=table,rank=r,peak=peak,probes=probes),work

def reopen(P,x,target=()):
    D,S,G,R=P['D'],P['S'],P['G'],P['rows'];I=set(D)
    if len(R)!=len(target) or not accepts(G,x):return None
    y=tuple((t-sum(a*b for i,(a,b) in enumerate(zip(row,x)) if i not in I))%3 for row,t in zip(R,target));k=P['image'].encode(y)
    if k is None:return None
    entry=P['table'].get((tuple(x[i] for i in S),k))
    if entry is None:return None
    d,N=entry;p=dict(zip(D,d))
    return tuple(p.get(i,b) for i,b in enumerate(x)),N

def histogram(F,cols,target,offset,R,cap,interior_width=24):
    """Exact original signed observer; extra image coordinate is the label."""
    R=tuple(sorted(R));n=len(cols);target=tuple(target)
    if not R:
        return ((0,0,0) if () in F or any(target) else tuple(int(d==offset%3) for d in range(3))),dict(work=0,rank=0)
    if () in F:return (0,0,0),dict(work=0,rank=0)
    rows=tuple(tuple(c[j] for c in cols) for j in range(len(target)+1))
    P,w=project(F,n,R,cap,rows,boundary_width=0,interior_width=interior_width)
    if P is None:return None,dict(work=w)
    assert not P['S'] and not P['G']
    H=[]
    for d in range(3):
        k=P['image'].encode(target+((d-offset)%3,));entry=P['table'].get(((),k))
        H.append(entry[1] if entry is not None else 0)
    return tuple(H),dict(work=w,rank=P['rank'],peak=P['peak'],probes=P['probes'])

def contrast(F,cols,target,offset,R,w,cap,interior_width=24):
    H,stats=histogram(F,cols,target,offset,R,cap,interior_width)
    if H is None:return None
    a=tuple(w*(3*h-sum(H)) for h in H)
    return a,a,dict(stats,head=H)
