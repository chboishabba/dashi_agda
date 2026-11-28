"""Intrinsic ternary syndrome boundary over disjoint nonlinear source blocks.
Reuse component histogram/RREF. Counts are original Boolean lifts, never
uniform F3 chart volume. All affine boundary labels and work are capped.
"""
from itertools import product
from functools import lru_cache
from math import isqrt
from check_pnp_signed_component_histogram import rref,component_bounds,convolve,energy

ZERO=(0,0,0)
def dot(a,b):return sum(x*y for x,y in zip(a,b))%3
def plus(a,b):return tuple((x+y)%3 for x,y in zip(a,b))
def minus(a,b):return tuple((x-y)%3 for x,y in zip(a,b))
def span(A,r):return tuple(row[:-1] for row in rref(tuple(tuple(a)+(0,) for a in A),r)[0])
def chart(A,b,r):
    rr=rref(tuple(tuple(a)+(t,) for a,t in zip(A,b)),r)
    if rr is None:return None
    rows,piv=rr;free=tuple(i for i in range(r) if i not in piv)
    u=[0]*r
    for i,row in zip(piv,rows):u[i]=row[-1]
    V=[]
    for j in free:
        v=[0]*r;v[j]=1
        for i,row in zip(piv,rows):v[i]=-row[j]%3
        V.append(tuple(v))
    return tuple(u),tuple(V)
def orth(A,r):return chart(A,(0,)*len(A),r)[1]
def ceilroot(n):
    q=isqrt(n);return q+int(q*q<n)

def blocks(F,R):
    parent={i:i for i in R}
    def root(i):
        while parent[i]!=i:parent[i]=parent[parent[i]];i=parent[i]
        return i
    for c in F:
        I=[abs(l)-1 for l in c]
        for j in I[1:]:parent[root(j)]=root(I[0])
    groups={}
    for i in R:groups.setdefault(root(i),[[],[]])[0].append(i)
    for c in F:groups[root(abs(c[0])-1)][1].append(c)
    return tuple((tuple(I),tuple(G)) for I,G in groups.values())

# A receipt is (exact retained histogram, omitted count cap, omitted
# character amplitude cap). Omitted mass is NOT an exact zero histogram.
def add_receipt(a,b):
    h,m,e=a;j,n,f=b
    return tuple(x+y for x,y in zip(h,j)),m+n,min(m+n,e+f)
def mul_receipt(a,b):
    h,m,e=a;j,n,f=b
    mass=sum(h)*n+sum(j)*m+m*n
    err=ceilroot(energy(h))*f+ceilroot(energy(j))*e+e*f
    return convolve(h,j),mass,min(mass,err)

class Refusal(Exception):pass

def syndrome_fold(F,cols,target,offset,R,local_width=6,boundary_width=3,work_cap=4096):
    """Return (receipt, stats) or (None,stats) on transactional refusal.
    Leaf labels are U_I intersect (target-U_complement); merge only additive
    compatible labels. No original variable occurs in two leaf blocks.
    Work counts candidate cuts, boundary labels, leaf point upper bounds,
    and compatible-pair probes. Linear algebra/bit overhead is separate.
    """
    R=tuple(sorted(R));r=len(target);target=tuple(target);stats=dict(work=0,width=0,leaf_labels=0,pairs=0,blocks=0)
    def pay(n):
        if stats['work']+n>work_cap:raise Refusal('work')
        stats['work']+=n
    if () in F:return (ZERO,0,0),stats
    G=blocks(F,R);m=len(G);stats['blocks']=m
    if not m:return (tuple(int(d==offset%3) for d in range(3)) if not any(target) else ZERO,0,0),stats
    if m==1:return None,dict(stats,reason='one nonlinear block')
    full=(1<<m)-1
    @lru_cache(None)
    def space(mask):
        pay(1)
        return span((cols[v][:-1] for j,(I,_) in enumerate(G) if mask>>j&1 for v in I),r)
    @lru_cache(None)
    def boundary(mask):
        pay(1);A=orth(space(mask),r);B=orth(space(full^mask),r)
        return chart(A+B,(0,)*len(A)+tuple(dot(b,target) for b in B),r)
    def rank(mask):
        q=boundary(mask);return -1 if q is None else len(q[1])
    def labels(mask):
        q=boundary(mask)
        if q is None:return
        u,V=q;d=len(V);stats['width']=max(stats['width'],d)
        if d>boundary_width:raise Refusal('width')
        pay(3**d)
        for t in product(range(3),repeat=d):
            yield tuple((x+sum(a*v[i] for a,v in zip(t,V)))%3 for i,x in enumerate(u))
    try:
        if rank(full)<0:return (ZERO,0,0),stats
        nodes=[(1<<i,None,None) for i in range(m)]
        # Same intrinsic greedy cut policy as the binary donor, with a
        # deterministic adjacent fallback for large independent-block sets.
        while len(nodes)>1:
            choices=((i,j) for i in range(len(nodes)) for j in range(i+1,len(nodes))) if len(nodes)<=12 else ((i,i+1) for i in range(len(nodes)-1))
            best=None
            for i,j in choices:
                pay(1);mask=nodes[i][0]|nodes[j][0];key=(rank(mask),mask.bit_count(),mask,i,j)
                if best is None or key<best:best=key
            _,_,mask,i,j=best;A,B=nodes[i],nodes[j];nodes.pop(j);nodes.pop(i);nodes.append((mask,A,B))
        def run(node):
            mask,A,B=node;admissible=set(labels(mask));T={}
            if not admissible:return T
            if A is None:
                I,F=G[mask.bit_length()-1];nullity=len(I)-len(space(mask))
                # Upper bound on explicit local enumeration; wide leaves use
                # certified caps instead. This is not a physical bit clock.
                cost=max(1,len(I))*2**min(local_width,nullity)
                for s in sorted(admissible):
                    pay(cost);stats['leaf_labels']+=1
                    done,C,H,E=component_bounds(F,cols,s,0,I,local_width,spectral=True)
                    if C:T[s]=(H,0,0) if done else (ZERO,C,min(C,ceilroot(E)))
                return T
            L=run(A);Q=run(B)
            for s,x in L.items():
                for t,y in Q.items():
                    pay(1);stats['pairs']+=1;u=plus(s,t)
                    if u in admissible:T[u]=add_receipt(T.get(u,(ZERO,0,0)),mul_receipt(x,y))
            return T
        h,mass,e=run(nodes[0]).get(target,(ZERO,0,0))
        return (tuple(h[(d-offset)%3] for d in range(3)),mass,e),stats
    except Refusal as e:return None,dict(stats,reason=str(e))

def syndrome_contrast(F,cols,target,offset,R,w,local_width=6,boundary_width=3,work_cap=4096):
    q,stats=syndrome_fold(F,cols,target,offset,R,local_width,boundary_width,work_cap)
    if q is None:return None
    H,C,E=q;head=tuple(w*(3*h-sum(H)) for h in H);radius=abs(w)*2*E
    return tuple(x-radius for x in head),tuple(x+radius for x in head),dict(stats,omitted_mass=C,amplitude=E,head=H)
