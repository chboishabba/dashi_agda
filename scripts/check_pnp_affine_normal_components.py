"""Exact normal-space component witness solver; bounded, never claims UNSAT externally."""
from itertools import combinations
from random import Random
from collections import Counter

class Exhausted(Exception): pass
class Budget:
    def __init__(self,cap): self.left=cap; self.stats=Counter()
    def pay(self,tag,n=1):
        self.left-=n; self.stats[tag]+=n
        if self.left<0: raise Exhausted

def bits(a):
    while a:
        b=a&-a; yield b.bit_length()-1; a^=b

def canon(rows):
    B={}
    for a,b in rows:
        for i in sorted(B,reverse=True):
            if a>>i&1:u,v=B[i];a^=u;b^=v
        if not a:
            if b:return None
            continue
        i=a.bit_length()-1
        for j,(u,v) in list(B.items()):
            if u>>i&1:B[j]=(u^a,v^b)
        B[i]=(a,b)
    return tuple(B[i] for i in sorted(B,reverse=True))

def satisfies(x,rows,flats):
    return all((a&x).bit_count()%2==b for a,b in rows) and all(any((a&x).bit_count()%2!=b for a,b in F) for F in flats)

def chart(n,R):
    piv={a.bit_length()-1:(a,b) for a,b in R}
    free=[i for i in range(n) if i not in piv]
    u=sum(b<<i for i,(a,b) in piv.items())
    V=[(1<<j)^sum(((a>>j)&1)<<i for i,(a,b) in piv.items()) for j in free]
    return u,V

def lift(u,V,y):
    for i in bits(y):u^=V[i]
    return u

def restrict(n,rows,F,B):
    R=canon(rows)
    if R is None:return None
    u,V=chart(n,R);out=[]
    for flat in F:
        G=canon((sum(((a&v).bit_count()%2)<<i for i,v in enumerate(V)), b^((a&u).bit_count()%2)) for a,b in flat)
        if G is not None:out.append(G)
        B.pay('restrict')
    return u,V,tuple(sorted(set(out)))

def simplify(F,B):
    """Union of forbidden flats: subsumption and parallel siblings only."""
    S=set(F)
    while True:
        if () in S:return ((),)
        for A,C in combinations(sorted(S),2):
            B.pay('coface')
            if len(A)>len(C):A,C=C,A
            if canon(A+C)==C:
                S.remove(C);break
            if tuple(a for a,b in A)==tuple(a for a,b in C):
                j=next(i for i,(a,b) in enumerate(A) if b!=C[i][1]);a,b=A[j]
                H=canon((u^a,v^b) if v!=C[i][1] else (u,v) for i,(u,v) in enumerate(A) if i!=j)
                S.remove(A);S.remove(C);S.add(H);break
        else:return tuple(sorted(S))

def split(n,F,B):
    """Independent normal basis; each forbidden flat connects its coordinate supports."""
    basis=[];echelon={}
    def express(a):
        z=0
        for i in sorted(echelon,reverse=True):
            if a>>i&1:v,c=echelon[i];a^=v;z^=c
        return a,z
    for G in F:
        for a,b in G:
            B.pay('basis');r,z=express(a)
            if r:
                i=r.bit_length()-1;echelon[i]=(r,z^(1<<len(basis)));basis.append(a)
    k=len(basis);parent=list(range(k));Q=[]
    def root(i):
        while parent[i]!=i:i=parent[i]
        return i
    for G in F:
        H=[];scope=0
        for a,b in G:
            r,z=express(a);assert r==0;H.append((z,b));scope|=z;B.pay('transport')
        H=canon(H);assert H is not None and scope
        q=list(bits(scope))
        for i in q[1:]:parent[root(i)]=root(q[0])
        Q.append((q[0],H))
    groups={}
    for i in range(k):groups.setdefault(root(i),[[],[]])[0].append(i)
    for i,H in Q:groups[root(i)][1].append(H)
    out=[]
    for I,G in groups.values():
        J={i:j for j,i in enumerate(I)}
        local=tuple(sorted(set(canon((sum(1<<J[i] for i in bits(a)),b) for a,b in H) for H in G)))
        out.append((I,local))
    return basis,out

def reopen(n,basis,y):
    R=canon((a,(y>>i)&1) for i,a in enumerate(basis));assert R is not None
    return chart(n,R)[0]

def solve(n,rows,F,B):
    """Exact answer internally if cap suffices, otherwise raises Exhausted. Cache only completed results."""
    B.pay('input',n+len(rows)+sum(len(G)+1 for G in F)+1)
    memo={}
    def go(n,F):
        B.pay('node',1+n+sum(len(G)+1 for G in F))
        F=simplify(F,B);key=(n,F)
        if key in memo:B.pay('cache_hit');return memo[key]
        if () in F:x=None
        elif not F:x=0
        elif satisfies(0,(),F):x=0
        else:
            units=tuple((G[0][0],G[0][1]^1) for G in F if len(G)==1)
            if units:
                q=restrict(n,units,F,B)
                if q is None:x=None
                else:
                    u,V,H=q;y=go(len(V),H);x=None if y is None else lift(u,V,y)
            else:
                basis,parts=split(n,F,B)
                if len(parts)>1 or len(basis)<n:
                    y=0
                    for I,H in parts:
                        v=go(len(I),H)
                        if v is None:y=None;break
                        y^=sum(((v>>j)&1)<<i for j,i in enumerate(I))
                    x=None if y is None else reopen(n,basis,y)
                else:
                    # Choose an actual source normal, not a count or a semantic oracle.
                    a=F[0][0][0];x=None
                    for b in (0,1):
                        B.pay('branch');u,V,H=restrict(n,((a,b),),F,B)
                        y=go(len(V),H)
                        if y is not None:x=lift(u,V,y);break
        if x is not None:assert satisfies(x,(),F)
        memo[key]=x;return x
    q=restrict(n,rows,F,B)
    if q is None:return None
    u,V,H=q;y=go(len(V),H)
    x=None if y is None else lift(u,V,y)
    if x is not None:assert satisfies(x,rows,F)
    return x

def recover(n,rows,F,cap):
    B=Budget(cap)
    try:x=solve(n,rows,F,B)
    except Exhausted:x=None
    return x,B.stats

def cnf_flats(f):
    return tuple(G for c in f if (G:=canon((1<<(abs(l)-1),int(l<0)) for l in c)) is not None)

def main():
    rng=Random(369);charts=cnfs=rewrites=verified=empty=0
    for n in range(9):
        for _ in range(80):
            rows=tuple((rng.randrange(1<<n),rng.randrange(2)) for _ in range(rng.randrange(n+1)))
            f=[tuple(rng.choice((-1,1))*i for i in rng.sample(range(1,n+1),rng.randrange(min(3,n)+1))) for _ in range(rng.randrange(10))]
            F=cnf_flats(f);truth=[x for x in range(1<<n) if satisfies(x,rows,F)]
            x,_=recover(n,rows,F,1000000);assert (x is not None)==bool(truth)
            if x is not None:assert x in truth;verified+=1
            else:empty+=1
            cnfs+=1
            G=tuple(A for _ in range(rng.randrange(9)) if (A:=canon((rng.randrange(1<<n),rng.randrange(2)) for _ in range(rng.randrange(1,n+2)))) is not None)
            s=simplify(G,Budget(1000000));assert all(satisfies(x,(),G)==satisfies(x,(),s) for x in range(1<<n));rewrites+=1
            truth=[x for x in range(1<<n) if satisfies(x,rows,G)]
            x,_=recover(n,rows,G,1000000);assert (x is not None)==bool(truth)
            if x is not None:assert x in truth
            if () not in s:
                basis,parts=split(n,s,Budget(1000000))
                for x in range(1<<n):
                    y=sum(((a&x).bit_count()%2)<<i for i,a in enumerate(basis))
                    assert satisfies(x,(),s)==all(satisfies(sum(((y>>i)&1)<<j for j,i in enumerate(I)),(),H) for I,H in parts)
                    z=reopen(n,basis,y);assert all((a&z).bit_count()%2==(a&x).bit_count()%2 for a in basis);charts+=1
    # Dense original normal coordinates: invertible matrix I + all-ones (even n).
    # Each local two-bit block excludes 00 only, so global support is 3^(n/2).
    for n in (8,16,32,64,128):
        normals=[((1<<n)-1)^(1<<i) for i in range(n)]
        F=tuple(canon(((normals[i],0),(normals[i+1],0))) for i in range(0,n,2))
        basis,parts=split(n,F,Budget(1000000));assert len(basis)==n and len(parts)==n//2 and all(len(I)==2 for I,H in parts)
        x,stats=recover(n,(),F,1000000);assert x is not None and satisfies(x,(),F)
        print('dense',n,'components',len(parts),'charged',sum(stats.values()),'cache_hits',stats['cache_hit'])
    # Connected original CNF+affine equations realizes same dense normal product.
    for n in (8,16,32,64):
        normals=[((1<<n)-1)^(1<<i) for i in range(n)]
        rows=tuple((normals[i]^(1<<(n+i)),0) for i in range(n))
        f=[(n+i+1,n+i+2) for i in range(0,n,2)]
        F=cnf_flats(f);x,stats=recover(2*n,rows,F,1000000);assert x is not None and satisfies(x,rows,F)
    assert recover(3,(),(),0)[0] is None
    assert recover(3,(),((),),10000)[0] is None
    print(dict(cnfs=cnfs,verified=verified,empty=empty,affine_sources=rewrites,pointwise_chart_checks=charts,stress=9,controls='PASS'))
if __name__=='__main__':main()
