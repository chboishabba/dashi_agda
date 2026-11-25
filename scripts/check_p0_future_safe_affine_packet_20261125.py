"""Exact affine parity packet with future-safe retirement; bounded frontier only."""
from itertools import product, combinations
from random import Random
from collections import defaultdict
import sympy as sp

def bits(m):
    while m:
        b=m&-m; yield b.bit_length()-1; m^=b

def canon(rows, preferred=0):
    B={}
    def key(i): return (bool(preferred>>i&1),i)
    for a,b in rows:
        for i in sorted(B,key=key,reverse=True):
            if a>>i&1: u,v=B[i]; a^=u; b^=v
        if not a:
            if b:return None
            continue
        i=max(bits(a),key=key)
        for j,(u,v) in list(B.items()):
            if u>>i&1:B[j]=(u^a,v^b)
        B[i]=(a,b)
    return tuple((i,*B[i]) for i in sorted(B,key=key,reverse=True))

def plain(rows):
    B=canon(rows)
    return None if B is None else tuple((a,b) for i,a,b in B)

def sat(x,f):return all(any(bool(x>>(abs(l)-1)&1)==(l>0) for l in c) for c in f)
def violate(c):return tuple((1<<(abs(l)-1),int(l<0)) for l in c)
def project(B,P,active,keep):
    """P=(constant, coefficient per original bit), each an (n+1)-bit vector."""
    if B is None:return None
    n=len(P)-1; dead=active&~keep
    R=canon(B,dead); assert R is not None
    p=list(P); piv=0; out=[]
    for i,a,b in R:
        if dead>>i&1:
            piv|=1<<i; v=p[i+1];p[i+1]=0
            if b:p[0]^=v
            for j in bits(a^(1<<i)):p[j+1]^=v
        else:out.append((a,b))
    free=dead&~piv
    if free.bit_count()>=2:return None
    if free:
        p=[p[free.bit_length()]]+[0]*n
    B=plain(out)
    # Normalize packet on the projected affine carrier before merging.
    for a,b in B:
        i=a.bit_length()-1;v=p[i+1];p[i+1]=0
        if b:p[0]^=v
        for j in bits(a^(1<<i)):p[j+1]^=v
    assert all(not p[i+1] for i in range(n) if not keep>>i&1)
    return (B,tuple(p)) if any(p) else None

def contract(n,rows,f,cap=100000):
    B=plain(rows);active=(1<<n)-1; suffix=[0]*(len(f)+1)
    for j in range(len(f)-1,-1,-1):
        suffix[j]=suffix[j+1]
        for l in f[j]:suffix[j]|=1<<(abs(l)-1)
    P=(1,)+tuple(1<<(i+1) for i in range(n))
    item=project(B,P,active,suffix[0]);active=suffix[0]
    S={} if item is None else {item[0]:item[1]};peak=len(S)
    for j,c in enumerate(f):
        T={}
        for B,P in S.items():
            for R in (B,plain(B+violate(c))):
                item=project(R,P,active,suffix[j+1])
                if item is None:continue
                K,V=item; V=tuple(a^b for a,b in zip(T.get(K,(0,)*(n+1)),V))
                if any(V):T[K]=V
                elif K in T:del T[K]
        S=T;active=suffix[j+1];peak=max(peak,len(S))
        if len(S)>cap:return None,peak
    assert set(S)<= {()}
    return S.get((),(0,))[0],peak

def reference(n,rows,f):
    p=0;count=0
    for x in range(1<<n):
        if sat(x,f) and all((a&x).bit_count()%2==b for a,b in rows):p^=1|(x<<1);count+=1
    return p,count

def full_rank_terms(n,f):
    S={()}
    for c in f:
        T=set(S)
        for B in S:
            K=plain(B+violate(c))
            if K is not None:T.symmetric_difference_update([K])
        S=T
    return sum(len(B)==n for B in S)

def main():
    rng=Random(88); stats=defaultdict(int)
    for n in range(0,9):
        for _ in range(80):
            rows=tuple((rng.randrange(1<<n),rng.randrange(2)) for _ in range(rng.randrange(n+1)))
            f=[tuple(rng.choice((-1,1))*i for i in rng.sample(range(1,n+1),rng.randrange(min(n,3)+1))) for _ in range(rng.randrange(8))]
            p,c=reference(n,rows,f);q,peak=contract(n,rows,f);assert p==q
            stats['random']+=1;stats['singleton']+=c==1;stats['max_peak']=max(stats['max_peak'],peak)
            rng.shuffle(f);assert contract(n,rows,f)[0]==p;stats['reordered']+=1
    # Seven-point incidence: multiplication by a primitive field element in GF(8).
    def mul2(x):return ((x<<1)^ (0b1011 if x&4 else 0))&7
    lines={tuple(sorted((a,b,a^b))) for a,b in combinations(range(1,8),2)}
    assert len(lines)==7 and {tuple(sorted(map(mul2,L))) for L in lines}==lines
    for _ in range(128):
        f=[tuple(rng.choice((-1,1))*i for i in L) for L in sorted(lines)]
        p,c=reference(7,(),f);assert contract(7,(),f)[0]==p
        g=[tuple((1 if l>0 else -1)*mul2(abs(l)) for l in C) for C in f]
        moved=(p&1)|sum(1<<mul2(i) for i in range(1,8) if p>>i&1)
        assert contract(7,(),g)[0]==moved;stats['fano']+=1
    # Find an explicit easy singleton block with >=3 full-rank IE terms.
    n=3;clauses=[tuple((1 if b>>j&1 else -1)*i for j,i in enumerate(I)) for k in (1,2,3) for I in combinations(range(1,n+1),k) for b in range(1<<k)]
    fixture=None
    for _ in range(5000):
        f=rng.sample(clauses,rng.randrange(4,10));p,c=reference(n,(),f)
        if c==1 and full_rank_terms(n,f)>=3:fixture=f;break
    assert fixture is not None
    t=full_rank_terms(n,fixture);p,c=reference(n,(),fixture)
    print('block',fixture,'full_rank_terms',t,'witness',p>>1)
    for blocks in (1,2,4,8,16,32):
        f=[tuple((1 if l>0 else -1)*(abs(l)+3*j) for l in C) for j in range(blocks) for C in fixture]
        q,peak=contract(3*blocks,(),f);assert q==1|sum((p>>1)<<(3*j+1) for j in range(blocks)); print('blocks',blocks,'projected_peak',peak,'unprojected_terminal_terms',t**blocks)
    # Equal low-order global packet, different suffix responses.
    # {00,01,10,11} and empty have equal parity and bit-XOR; pin both bits => one vs zero.
    assert reference(2,(),[])[0]==reference(2,(),[()])[0]==0
    assert reference(2,(),[(1,),(2,)])[0]!=reference(2,(),[(),(1,),(2,)])[0]
    a,b,c,d=sp.symbols('a b c d');assert sp.expand((a+b)*(c+d)-(a*c+a*d+b*c+b*d))==0
    print(dict(stats))
if __name__=='__main__':main()
