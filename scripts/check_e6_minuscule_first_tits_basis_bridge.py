#!/usr/bin/env python3
"""Exact finite bridge: E8->E6 minuscule 27 weights <-> first-Tits M3^3 basis labels.

This composes two already-paid lanes on the stacked #1098/#1106 branch:
  * the 27-weight E6 Weyl action extracted from the E8 mixed fibre;
  * the literal first-Tits 3x3x3 basis, whose A2^3 Cartan weights are explicit.

The script proves at execution grade that the two 27-point weight graphs are
isomorphic, transports the six E6 generating reflections to the first-Tits
basis labels, and re-generates the full 51,840-element permutation image.

This is a finite weight/basis-LABEL action bridge.  It does not yet construct
chosen linear Weyl representatives on the rational Albert vector space: the
1-dimensional weight spaces still carry an unresolved nonzero scalar/phase
cocycle under such representatives.
"""
from collections import defaultdict, deque
from fractions import Fraction as F
from itertools import product
import json


def dot(x,y): return sum(a*b for a,b in zip(x,y))
def reflect(v,r):
    c=2*dot(v,r)/dot(r,r);return tuple(x-c*a for x,a in zip(v,r))
def compose(p,q): return tuple(p[q[i]] for i in range(len(p)))

def e8_roots():
    roots=[]
    for i in range(8):
        for j in range(i+1,8):
            for si,sj in product((-2,2),repeat=2):
                x=[0]*8;x[i]=si;x[j]=sj;roots.append(tuple(F(v) for v in x))
    for signs in product((-1,1),repeat=8):
        if sum(v<0 for v in signs)%2==0:roots.append(tuple(F(v) for v in signs))
    return roots

def rank(vs):
    rows=[list(v) for v in vs]
    if not rows:return 0
    m,n=len(rows),len(rows[0]);r=c=0
    while r<m and c<n:
        p=next((i for i in range(r,m) if rows[i][c]),None)
        if p is None:c+=1;continue
        rows[r],rows[p]=rows[p],rows[r];q=rows[r][c];rows[r]=[x/q for x in rows[r]]
        for i in range(m):
            if i!=r and rows[i][c]:q=rows[i][c];rows[i]=[x-q*y for x,y in zip(rows[i],rows[r])]
        r+=1;c+=1
    return r

def e6_side():
    roots=e8_roots();av=lambda r:sum(r[5:])/3
    e6=[r for r in roots if r[5:] in ((F(-1),)*3,(F(0),)*3,(F(1),)*3)]
    a2=[r for r in roots if sorted(r[5:])==[F(-2),F(0),F(2)]];mixed=[r for r in roots if r not in e6 and r not in a2]
    def key(r):a=av(r);return tuple(v-a for v in r[5:])
    fibres=defaultdict(list)
    for r in mixed:fibres[key(r)].append(r)
    fibre=fibres[sorted(fibres)[0]]
    def proj(r):a=av(r);return tuple(r[:5])+(a,a,a)
    weights=sorted({proj(r) for r in fibre});idx={w:i for i,w in enumerate(weights)};e6set=set(e6)
    adj=[[False]*27 for _ in range(27)]
    for i,w in enumerate(weights):
        for j,z in enumerate(weights):
            if i!=j and tuple(a-b for a,b in zip(w,z)) in e6set:adj[i][j]=True
    simple=[]
    for r in e6:
        if rank(simple+[r])>len(simple):simple.append(r)
        if len(simple)==6:break
    gens=[tuple(idx[reflect(w,r)] for w in weights) for r in simple]
    return weights,adj,gens

def first_tits_side():
    h1=(1,-1,0);h2=(0,1,-1);weights=[];labels=[]
    for i in range(3):
        for j in range(3):weights.append((h1[i],h2[i],-h1[j],-h2[j],0,0));labels.append(('X',i,j))
    for i in range(3):
        for j in range(3):weights.append((0,0,h1[i],h2[i],-h1[j],-h2[j]));labels.append(('Y',i,j))
    for i in range(3):
        for j in range(3):weights.append((-h1[j],-h2[j],0,0,h1[i],h2[i]));labels.append(('Z',i,j))
    # Three inverse-A2 Cartan blocks, scaled by 3. Squared distance 2 => q=6.
    def q(v):return sum(2*v[2*b]**2+2*v[2*b+1]**2+2*v[2*b]*v[2*b+1] for b in range(3))
    adj=[[False]*27 for _ in range(27)]
    for i,w in enumerate(weights):
        for j,z in enumerate(weights):
            if i!=j:adj[i][j]=(q(tuple(a-b for a,b in zip(w,z)))==6)
    return weights,labels,adj

def find_iso(a,b):
    n=len(a);mapping={0:0};used={0}
    def compat(i,t):return all(a[i][j]==b[t][u] for j,u in mapping.items())
    def choose():
        best=None
        for i in range(n):
            if i in mapping:continue
            cand=[t for t in range(n) if t not in used and compat(i,t)]
            if best is None or len(cand)<len(best[1]):best=(i,cand)
        return best
    def dfs():
        if len(mapping)==n:return True
        i,cand=choose()
        for t in cand:
            mapping[i]=t;used.add(t)
            if dfs():return True
            used.remove(t);del mapping[i]
        return False
    assert dfs();return mapping

def group_closure(gens):
    I=tuple(range(len(gens[0])));seen={I};q=deque([I])
    while q:
        g=q.popleft()
        for s in gens:
            h=compose(s,g)
            if h not in seen:seen.add(h);q.append(h)
    return seen

def main():
    e8weights,a,gens=e6_side();titsweights,labels,b=first_tits_side()
    assert all(sum(row)==16 for row in a);assert all(sum(row)==16 for row in b)
    iso=find_iso(a,b);inv={v:k for k,v in iso.items()}
    transported=[]
    for g in gens:transported.append(tuple(iso[g[inv[t]]] for t in range(27)))
    assert all(all(b[g[i]][g[j]]==b[i][j] for i in range(27) for j in range(27)) for g in transported)
    group=group_closure(transported);assert len(group)==51840
    result={'nodes':27,'degree':16,'edges':216,'explicit_graph_isomorphism_e8_index_to_first_tits_index':{str(k):v for k,v in iso.items()},'first_tits_labels':[list(x) for x in labels],'transported_six_generators':[list(g) for g in transported],'generated_permutation_group_order':len(group),'finite_weight_basis_label_action_paid':True,'linear_weight_space_scalar_cocycle_paid':False}
    print(json.dumps(result,indent=2))
if __name__=='__main__':main()
