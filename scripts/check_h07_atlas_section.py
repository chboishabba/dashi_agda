#!/usr/bin/env python3
"""H07 full finite atlas sections and literal H05 codec naturality.
Exact bounded integer F3 arithmetic; no kernel or physical/Monster claim.
"""
from itertools import combinations, product, permutations
from collections import Counter
import numpy as np

def require(ok, label):
    if not bool(ok): raise RuntimeError(label)
marks=tuple(combinations(range(5),2)); tr=np.array(list(product(range(3),repeat=3)),dtype=np.int64)
I=np.eye(5,dtype=np.int64)
W={p:np.array([int(i not in p) for i in range(5)],dtype=np.int64) for p in marks}
comps={p:tuple(i for i in range(5) if i not in p) for p in marks}
def pack(p,a,b):
    B=np.zeros((5,2),dtype=np.int64); B[list(p)]=np.eye(2,dtype=np.int64); B[list(comps[p])]=np.stack((a,b),axis=1); return B
def project(B,q):
    a,b=B[q[0]]; c,d=B[q[1]]; det=int((a*d-b*c)%3)
    if det==0:return None
    inv=det*np.array([[d,-b],[-c,a]],dtype=np.int64)
    return (I-B@inv@I[list(q)])%3

def rotation(p):
    # Literal rotateTriple(a,b,c)=(b,c,a) on the anchor complement.
    c=comps[p]; order=list(range(5))
    for i,j in zip(c,c[1:]+c[:1]):order[i]=j
    return tuple(order)

def moved(q,order):return tuple(sorted(order.index(i) for i in q))
# Enumerate all directions via canonical minimal admissible pivot.
counts=Counter(); marked=0; bad_fixed=0; zero_phase=0
for p,a,b in product(marks,tr,tr):
    B=pack(p,a,b)
    charts={q:P for q in marks if (P:=project(B,q)) is not None}
    if p!=min(charts):continue
    counts['directions']+=1; qs=tuple(charts); k=len(qs); marked+=k
    Ps=np.stack([charts[q] for q in qs]); ws=np.stack([W[q] for q in qs]);
    # All 27 base offsets at canonical pivot, all 3 winding residues, all anchors.
    X=tr@I[list(comps[p])]; n=np.arange(3,dtype=np.int64)
    # shape (anchor, offset, winding, coordinate)
    actual=(X[None,:,None,:]+n[None,None,:,None]*ws[:,None,None,:])%3
    # Independently construct every local chart vertex's uncorrected value and
    # its full signed anchor correction. Shape (anchor,local,offset,winding,5).
    local_input=(X[None,:,None,:]+n[None,None,:,None]*ws[:,None,None,:])%3
    raw=np.einsum('vij,vxnj->vxni',Ps,local_input)%3
    corr=np.einsum('vij,avj->avi',Ps,(ws[:,None,:]-ws[None,:,:]))%3
    r=(corr[:,:,None,None,:]*n[None,None,None,:,None])%3
    fixed=(raw[None,:,:,:,:]+r)%3
    expected=np.einsum('qij,axnj->aqxni',Ps,actual)%3
    require(np.array_equal(fixed,expected),'vertex correction vs original ambient')
    require(np.array_equal((fixed-r)%3,np.broadcast_to(raw[None,:,:,:,:],fixed.shape)),'recover local raw')
    # Edge q is normalized in q. Every local v restricts to that SAME edge,
    # retaining its own correction in vertex, and common anchor-indexed ledger.
    restrictions=np.einsum('qij,avxnj->avqxni',Ps,fixed)%3
    require(np.array_equal(restrictions,np.broadcast_to(expected[:,None,:,:,:,:],restrictions.shape)),'all incident restrictions')
    # Common edge ledger of all local residuals; do not equate these with
    # each other or delete them just because corrected values agree.
    transported=np.einsum('qij,avj->avqi',Ps,corr)%3
    ledger=np.einsum('qij,avj->avqi',Ps,ws[:,None,:]-ws[None,:,:])%3
    require(np.array_equal(transported,ledger),'full indexed residual ledger')
    # Recover original anchor base from its corrected translated value.
    recovered=(fixed[np.arange(k),np.arange(k)]-n[None,None,:,None]*ws[:,None,None,:])%3
    require(np.array_equal(recovered,np.broadcast_to((np.einsum('aij,xj->axi',Ps,X)%3)[:,:,None,:],recovered.shape)),'anchor offset BIDI')
    counts['ledger_checks']+=k**3
    counts['sections']+=k*27*3; counts['incidence_checks']+=k**3*27*3
    counts['vertex_checks']+=k*k*27*3
    # Direction-level covariance of every projection and signed seam under
    # the literal anchor-local rotation; check all marks including singular.
    for ai,anchor in enumerate(qs):
        order=rotation(anchor); T=I[list(order)]; BB=T@B
        target={q:project(BB,q) for q in marks}
        for vi,v in enumerate(qs):
            q=moved(v,order); P=target[q]
            require(P is not None and np.array_equal((P@T)%3,(T@Ps[vi])%3),'projection naturality')
            require(np.array_equal(W[q],T@ws[vi]),'phase direction naturality')
            cc=P@(W[anchor]-W[q])%3
            require(np.array_equal(cc,T@corr[ai,vi]%3),'signed correction naturality')
            counts['rotation_checks']+=1
            if v!=anchor and target[v] is None:bad_fixed+=1
            # all 27 offsets and residues, actual translated endpoints
            require(np.array_equal(np.einsum('ij,xnj->xni',P,np.einsum('ij,xnj->xni',T,actual[ai]))%3,np.einsum('ij,xnj->xni',T,expected[ai,vi])%3),'rotated restriction')
        for q in marks:
            require((target[moved(q,order)] is not None)==(q in charts),'singular transported guard')
            counts['guard_checks']+=1
require(counts['directions']==1210 and marked==7290,'atlas census')
require(counts['sections']==590490,'marked/winding sections')
require(bad_fixed>0,'fixed target guard negative control')
# Actual H05 codec arrows, on every raw marked coefficient state. X retains
# suffix in a distinct split structure, Y rotates triples, Z retains support/sign.
raw=np.array(list(product(range(3),repeat=9)),dtype=np.int64).reshape(-1,3,3)
# Tag original mark separately, all operations fix it; geometric Y is above.
def op(s,c):
    prefix,encoded,data=s
    if c=='x':
        require(not prefix,'partition twice'); return (True,encoded,(data[:,:2],data[:,2:]))
    if c=='y':
        return (prefix,encoded,tuple(np.roll(a,-1,axis=2) for a in data) if prefix else np.roll(data,-1,axis=2))
    if c=='z':
        require(not encoded,'encode twice')
        def enc(a):return np.stack((a!=0,np.where(a==2,-1,a)),axis=-1)
        return (prefix,True,tuple(enc(a) for a in data) if prefix else enc(data))
def path(s,order):
    for c in order:s=op(s,c)
    return s
def equal(a,b):
    return a[:2]==b[:2] and (all(np.array_equal(x,y) for x,y in zip(a[2],b[2])) if a[0] else np.array_equal(a[2],b[2]))
s=(False,False,raw)
for a,b,c in [('x','y','z'),('x','z','y'),('y','z','x')]:
    for pre in ('',c):require(equal(path(s,pre+a+b),path(s,pre+b+a)),'literal codec face')
end=path(s,'xyz')
for order in permutations('xyz'):require(equal(end,path(s,order)),'literal codec endpoint')
rejoined=np.concatenate(end[2],axis=1); require(np.array_equal(rejoined[...,0],rejoined[...,1]!=0),'support sign consistency')
require(np.array_equal(rejoined[...,1]%3,np.roll(raw,-1,axis=2)),'reopen full signed suffix')
print('PASS full atlas',dict(counts),'marked directions',marked,'fixed-target singular cases',bad_fixed)
print('PASS six literal codec faces and paths',len(raw)*len(marks)*6,'each (identical coefficient test reused on 10 marks)')
print('PASS geometry/restriction covariance independent of codec representation; all 27 cosets and 3 residues executed')
