#!/usr/bin/env python3
"""Exact finite H07 corrected affine restrictions; selected pants observation.
No physical wave, C3=Phase4 identification, or Monster action claimed.
"""
from itertools import combinations, product
from collections import Counter

def require(ok, label):
    if not ok: raise RuntimeError(label)
F=range(3); marks=tuple(combinations(range(5),2)); triples=tuple(product(F,repeat=3))
def add(x,y): return tuple((a+b)%3 for a,b in zip(x,y))
def sub(x,y): return tuple((a-b)%3 for a,b in zip(x,y))
def mul(n,x): return tuple(n*a%3 for a in x)
def w(p): return tuple(int(i not in p) for i in range(5))
def pack(p,a,b):
    v=[0]*5; u=[0]*5; v[p[0]]=1; u[p[1]]=1
    for j,i in enumerate(k for k in range(5) if k not in p): v[i]=a[j]; u[i]=b[j]
    return tuple(v),tuple(u)
def basis(v,u,q):
    i,j=q; d=(v[i]*u[j]-v[j]*u[i])%3
    if not d:return None
    return mul(d,sub(mul(u[j],v),mul(v[j],u))),mul(d,sub(mul(v[i],u),mul(u[i],v)))
def proj(x,B,q):
    a,b=B; return sub(x,add(mul(x[q[0]],a),mul(x[q[1]],b)))
def mid(p):return 3*sum(p)%5
def bal(x):return x if x!=2 else -1
def wave(x,q):
    a,b,c=(bal(x[i]) for i in range(5) if i not in q)
    return (a+3*b,c)
def interface(x,q,phase=0): return ('selected affine plane offset',9,phase,wave(x,q),True)
counts=Counter(); residuals=Counter(); phase_checks=0
for p,a,b in product(marks,triples,triples):
    B=pack(p,a,b); charts={q:C for q in marks if (C:=basis(*B,q)) is not None}
    for q,C in charts.items():
        if p==q:continue
        c=proj(sub(w(p),w(q)),C,q); reverse=proj(sub(w(q),w(p)),B,p)
        require(reverse==mul(2,proj(c,B,p)),'signed inverse')
        paired=mid(p)==mid(q) and not(set(p)&set(q))
        for n in F:
            r=mul(n,c); expected=proj(mul(n,w(p)),C,q); raw=mul(n,w(q)); corrected=add(raw,r)
            require(corrected==expected,'corrected edge restriction')
            require(sub(corrected,r)==raw,'raw recovery')
            require(proj(corrected,B,p)==mul(n,w(p)),'reverse chart')
            # Offset arbitrary by linearity, independent of the phase defect.
            counts['directed winding checks']+=1
            if paired:
                counts['paired winding checks']+=1; counts['paired raw matches']+=raw==expected
                residuals[(n,tuple(r[i] for i in range(5) if i not in q))]+=1
                for phase4 in range(4):
                    require(interface(corrected,q,phase4)==interface(expected,q,phase4),'five interface fields')
                    require((interface(raw,q,phase4)==interface(expected,q,phase4))==(not any(r)),'wave detects seam discrepancy')
                    phase_checks+=1
# Literal witness on pair 01/24; all 27 offsets and three signed F3 residues.
p=(0,1);q=(2,4);B=pack(p,(1,0,0),(0,0,1));C=basis(*B,q)
require(C is not None,'witness overlap'); c=proj(sub(w(p),w(q)),C,q)
require(c==(1,1,0,0,0),'witness residual')
for a,b,d in triples:
    x=(0,0,a,b,d)
    for n in F:
        local=proj(add(x,mul(n,w(q))),C,q); actual=proj(add(x,mul(n,w(p))),C,q)
        require(add(local,mul(n,c))==actual,'all witness offsets')
        require(sub(actual,mul(n,c))==local,'witness reverse')
require(counts==Counter({'directed winding checks':126360,'paired winding checks':12960,'paired raw matches':4680}),'counts')
require(phase_checks==51840,'phase4 checks')
# Signed balanced radix wave is injective on the 27 q offsets.
require(len({wave((a,b,0,c,0),q) for a,b,c in triples})==27,'wave injective')
print('PASS',dict(counts),'five-field checks',phase_checks)
print('distinct paired corrections by winding',Counter({n:len([x for k,x in residuals if k==n]) for n in F}))
print('PASS 81 literal offset/winding cases, signed inverse, injective finite wave observer')
