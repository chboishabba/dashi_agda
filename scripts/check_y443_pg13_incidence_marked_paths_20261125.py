#!/usr/bin/env python3
"""Y443 source tree and JMD path graph certificates in typed PG(2,3) incidence.
No group/VOA, physical, or kernel acceptance. Finite exact integers only.
"""
from itertools import product, combinations
from collections import Counter

def require(ok, label):
    if not ok:
        raise RuntimeError(label)

T = list(product((-1,0,1), repeat=3))
neg = lambda v: tuple(-x for x in v)
canon = lambda v: min(v, neg(v))
P = sorted({canon(v) for v in T if any(v)})
r = canon((1,1,1))
sw = lambda v: canon((v[1],v[0],v[2]))
dot = lambda v,w: sum(a*b for a,b in zip(v,w))
E = {(0,1),(1,2),(2,3),(3,4),(0,5),(5,6),(6,7),(7,8),(0,9),(9,10),(10,11)}
JMD = [(11,10,9,0,1,2,3,4),(5,6,7,8),(0,5,6,7,8)]

def census(A, root, swap, induced=False):
    def paths(v,k):
        if not k:
            yield (v,); return
        for u in sorted(A[v]):
            for p in paths(u,k-1):
                if v not in p:
                    yield (v,)+p
    def clean(p):
        return not induced or all(p[j] not in A[p[i]] for i,j in combinations(range(len(p)),2) if j-i>1)
    def compatible(p,q):
        return not(set(p[1:])&set(q[1:])) and (not induced or all(w not in A[v] for v in p[1:] for w in q[1:]))
    long = [p for p in paths(root,4) if clean(p)]
    short = [p for p in paths(root,3) if clean(p)]
    all_maps, equiv = [], []
    for p in long:
        for q in long:
            if not compatible(p,q): continue
            for t in short:
                if not (compatible(p,t) and compatible(q,t)): continue
                n=(root,*p[1:],*q[1:],*t[1:]); all_maps.append(n)
                if tuple(map(swap,p))==q and tuple(map(swap,t))==t: equiv.append(n)
    return all_maps,equiv

N = {p:{canon(w) for v in (p,neg(p)) for w in T if any(w) and sum(abs(a-b) for a,b in zip(v,w))==1} for p in P}
B = {p:{q for q in P if p!=q and dot(p,q)%3==0} for p in P}
V = [(k,p) for k in (0,1) for p in P]
L = {v:{w for w in V if v[0]!=w[0] and dot(v[1],w[1])%3==0} for v in V}
require(len(P)==13 and sum(map(len,L.values()))==104,'incidence census')
n,ns=census(N,r,sw); b,bs=census(B,r,sw)
l,ls=census(L,(0,r),lambda v:(v[0],sw(v[1])),True)
require((len(n),len(ns),len(b),len(bs),len(l),len(ls))==(600,0,456,8,432,12),'embedding census')
for m in l:
    require(all((m[j] in L[m[i]])==((i,j) in E) for i,j in combinations(range(12),2)),'induced pair')
    for p in JMD:
        require(all((m[p[j]] in L[m[p[i]]])==(j-i==1) for i,j in combinations(range(len(p)),2)),'JMD source path')
    require(all(m[i] not in L[m[4]] for i in (5,6,7,8)),'JMD x4 beta nonedges')
real=[m for m in ls if all(dot(m[i][1],m[j][1])==0 for i,j in E)]
require(len(real)==8,'real incidence witnesses')
for m in real:
    require(all((dot(m[i][1],m[j][1])==0)==((i,j) in E) for i,j in combinations(range(12),2) if m[i][0]!=m[j][0]),'typed real induced incidence')
C=list(product((-1,1),repeat=3)); root=(1,1,1)
def flip(v,k): return tuple(-x if j==k else x for j,x in enumerate(v))
def trace(v,w):
    out=[v]
    for k in w: out.append(flip(out[-1],k))
    return out
W=[w for w in product(range(3),repeat=8) if (vs:=trace(root,w))[-1]==root and len(set(vs[:-1]))==8]
G=[(k,d) for k in range(3) for d in C if d[0]*d[1]*d[2]==1]
def act(g,v):
    k,d=g; return tuple(d[i]*v[(i-k)%3] for i in range(3))
M={(v,w) for v in C if v[0]*v[1]*v[2]==1 for w in W}
def moved(g,m): return act(g,m[0]),tuple((i+g[0])%3 for i in m[1])
def edge(m): return tuple((a+b)//2 for a,b in zip(m[0],flip(m[0],m[1][0])))
require(len(W)==12 and len(M)==48,'marked paths')
require(Counter(sum(moved(g,m)==m for m in M) for g in G)==Counter({0:11,48:1}),'free marked action')
require(Counter(Counter(map(edge,M)).values())==Counter({4:12}),'edge fibres')
require(all(edge(moved(g,m))==act(g,edge(m)) for g in G for m in M),'edge equivariance')
# Exact reconstruction: the missing sign is fixed by positive root parity;
# rank the four words with the required first coordinate in that edge's A4 frame.
base=(0,1,1)
frames={act(g,base):g for g in G}
words=sorted(w for w in W if w[0]==0)
require(len(frames)==12 and len(words)==4,'edge frames')
def encode(m):
    e=edge(m); k,_=frames[e]
    return e,words.index(tuple((i-k)%3 for i in m[1]))
def decode(code):
    e,j=code; g=frames[e]
    return moved(g,(root,words[j]))
require(all(decode(encode(m))==m for m in M),'marked reverse')
require(all(encode(moved(g,m))==(act(g,edge(m)),encode(m)[1]) for g in G for m in M),'residual equivariance')
print('PASS native 600/0, polarity 456/8, Levi induced 432/12, real 8')
print('PASS 432*66 pair comparisons, original JMD paths/nonedges; witness',real[0])
print('PASS 48 marked paths, 12 edge centres x 4 residuals, 576 action cases')
