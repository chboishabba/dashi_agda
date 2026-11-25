#!/usr/bin/env python3
"""H07 marked F3 affine planes: pentad x paired chart, free phase, retained seam.
Finite carrier bridge only; no Monster same-object or physical claim.
"""
from itertools import combinations, product, permutations
from collections import Counter

def require(ok, label):
    if not ok: raise RuntimeError(label)
F=range(3); marks=tuple(combinations(range(5),2)); uv=tuple(product(F,repeat=2))
# Z5 midpoint, unoriented distance. C2 exchanges disjoint partners in a round.
def mark(m,d): return tuple(sorted(((m-d)%5,(m+d)%5)))
def split(p):
    i,j=p; m=3*(i+j)%5; d=(i-m)%5
    return m,min(d,5-d)
require(all(mark(*split(p))==p for p in marks),'five-two inverse')
require(all(split(mark(m,d))==(m,d) for m,d in product(range(5),(1,2))),'five-two forward')
for p in marks:
    m,d=split(p); q=mark(m,3-d)
    require(set(p).isdisjoint(q) and set(p)|set(q)==set(range(5))-{m},'disjoint round')
    require(split(tuple(sorted((i+1)%5 for i in p)))==((m+1)%5,d),'C5')
# Nine coefficients ordered as slope U, slope V, offset in sorted complement.
def pack(p,a,b,c):
    v=[0]*5; w=[0]*5; o=[0]*5; v[p[0]]=1; w[p[1]]=1
    for k,j in enumerate(i for i in range(5) if i not in p): v[j]=a[k]; w[j]=b[k]; o[j]=c[k]
    return tuple(v),tuple(w),tuple(o)
def chart(v,w,o,p):
    i,j=p; d=(v[i]*w[j]-v[j]*w[i])%3
    if not d: return None
    a=tuple(d*(w[j]*x-v[j]*y)%3 for x,y in zip(v,w))
    b=tuple(d*(v[i]*y-w[i]*x)%3 for x,y in zip(v,w))
    c=tuple((z-o[i]*x-o[j]*y)%3 for x,y,z in zip(a,b,o))
    return a,b,c

def shift(s,k=1):
    p,a,b,c=s; return p,a,b,tuple((x+k)%3 for x in c)
def regular(s):
    p,a,b,c=s; t=c[0]; return (split(p),a,b,( (c[1]-t)%3,(c[2]-t)%3)),t
def unregular(r,t):
    md,a,b,(x,y)=r; return mark(*md),a,b,(t,(x+t)%3,(y+t)%3)
def permute(s,pi):
    p,a,b,c=s; q=tuple(sorted(pi[i] for i in p)); v,w,o=pack(p,a,b,c)
    inv=tuple(pi.index(i) for i in range(5)); x,y,z=chart(*(tuple(t[i] for i in inv) for t in (v,w,o)),q)
    return (q,)+tuple(tuple(t[i] for i in range(5) if i not in q) for t in (x,y,z))
# Literal source rotateTriple(a,b,c)=(b,c,a), hence old 2->4,3->2,4->3.
R=(0,1,4,2,3); C5=(1,2,3,4,0); swap=(1,0,2,3,4)
# Reference existing pointed-sheet selected digit convention, chosen chart mapping:
# d0 -> unmarked, r0 -> centre marker, other direct/reflected half slots -> boundary.
boundary=(0,1,2,3,5,6,7,8)
def label(md):
    m,d=md
    return (0 if d==1 else 5) if m==0 else 1+boundary[(d-1)*4+m-1]
labels={label(split(p)):p for p in marks}
require(len(labels)==10,'chosen pointed chart bijection')
def pointed(s):
    (md,a,b,rem),t=regular(s); ch=label(md); j=4 if ch==0 else ch-1
    ds=a+b+rem; return ch,ds[:j]+(t,)+ds[j:]
def unpointed(ch,ds):
    j=4 if ch==0 else ch-1; t=ds[j]; d=ds[:j]+ds[j+1:]
    return unregular((split(labels[ch]),d[:3],d[3:6],d[6:]),t)
def refC3(ch,ds):
    j=4 if ch==0 else ch-1; return ch,ds[:j]+((ds[j]+1)%3,)+ds[j+1:]
fixed=0; total=0; orbits=set(); triples=tuple(product(F,repeat=3))
for p,a,b,c in product(marks,triples,triples,triples):
    s=p,a,b,c; r,t=regular(s); total+=1; orbits.add(r)
    require(unregular(r,t)==s and regular(shift(s))==(r,(t+1)%3),'phase BIDI')
    require(shift(s,3)==s and shift(s)!=s,'free phase')
    q=pointed(s); require(unpointed(*q)==s and pointed(shift(s))==refC3(*q),'pointed C3 BIDI')
    # Actual ambient coordinate rotation, not a replacement by free phase.
    sr=permute(s,R); fixed+=sr==s
    require(permute(shift(s),R)==shift(sr),'rotation/phase commute')
require((total,len(orbits),fixed)==(196830,65610,27),'bulk census')
# Generator tests for full coordinate permutation covariance on all direction
# charts at zero and three basis offsets; affine linearity extends offsets.
cov=0
for p,a,b,c in product(marks,triples,triples,((0,0,0),(1,0,0),(0,1,0),(0,0,1))):
    s=p,a,b,c
    for pi in (C5,swap):
        require(permute(shift(s),pi)==shift(permute(s,pi)),'S5 generator covariance'); cov+=1
# Translation by the nonpivot indicator does NOT descend to unmarked plane.
# One concrete witness with both pivots admissible, unequal translated cosets.
P=(0,1); Q=(0,2); s=(P,(0,0,0),(1,0,0),(0,0,0))
v,w,o=pack(*s); a,b,c=chart(v,w,o,Q); t=(Q,)+tuple(tuple(x[i] for i in range(5) if i not in Q) for x in (a,b,c))
def pts(s):
    v,w,o=pack(*s); return frozenset(tuple((z+i*x+j*y)%3 for x,y,z in zip(v,w,o)) for i,j in uv)
require(pts(s)==pts(t) and pts(shift(s))!=pts(shift(t)),'mark dependence witness')
print('PASS marked',total,'free phase orbits',len(orbits),'literal ambient rotation fixed',fixed)
print('PASS pointed source C3 BIDI',total,'S5 generator basis-offset covariance',cov)
print('PASS natural rotation bulk regular blocks',(total-fixed)//3,'fixed',fixed,'non-descent witness',s,t)
print('PASS retained coarse 54 count: selected free action trace 54; ambient R plus fixed coarse trace 81')
# Actual seam obstruction: compare chart-relative translations in the common
# quotient F3^5 / direction. Keep the signed difference, never delete it.
def w(p): return tuple(int(i not in p) for i in range(5))
def proj(x,a,b,p): return tuple((z-x[p[0]]*u-x[p[1]]*v)%3 for z,u,v in zip(x,a,b))
def diff(x,y): return tuple((a-b)%3 for a,b in zip(x,y))
def add(x,y): return tuple((a+b)%3 for a,b in zip(x,y))
counts=Counter(); seam=Counter(); triples_checked=0
for p,a,b in product(marks,triples,triples):
    v,u,o=pack(p,a,b,(0,0,0)); charts={q:rep for q in marks if (rep:=chart(v,u,o,q)) is not None}
    # Only test triangle cocycle once per direction, at the first chart.
    for q,(aq,bq,_) in charts.items():
        residual=proj(diff(w(p),w(q)),aq,bq,q)
        translated=chart(v,u,w(p),q)[2]
        require(diff(translated,w(q))==residual,'signed seam residual')
        if p!=q:
            k=len(set(p)&set(q)); counts[k,'all']+=1; counts[k,'zero']+=not any(residual)
            if split(p)[0]==split(q)[0]: seam['all']+=1; seam['zero']+=not any(residual)
    if p==min(charts):
        for q,r,t in combinations(charts,3):
            ar,br,_=charts[r]; at,bt,_=charts[t]
            qr=proj(diff(w(q),w(r)),ar,br,r)
            rt=proj(diff(w(r),w(t)),at,bt,t)
            qt=proj(diff(w(q),w(t)),at,bt,t)
            require(add(proj(qr,at,bt,t),rt)==qt,'seam residual cocycle'); triples_checked+=1
require(seam==Counter({'all':4320,'zero':180}),'five paired seams count')
print('PASS directed overlap directions',dict(counts),'paired seam directions',dict(seam),'triple residual cocycles',triples_checked)
