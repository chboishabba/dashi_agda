"""Exact binary affine coface rewriting; capped frontier, not universal SAT."""
from itertools import combinations
from random import Random
from collections import Counter
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

def norm(B,P):
    p=list(P)
    for a,b in B:
        i=a.bit_length()-1;v=p[i+1];p[i+1]=0
        if b:p[0]^=v
        for j in bits(a^(1<<i)):p[j+1]^=v
    return tuple(p)

def project(B,P,active,keep):
    if B is None:return None
    n=len(P)-1; dead=active&~keep
    R=canon(B,dead); p=list(P); piv=0; out=[]
    for i,a,b in R:
        if dead>>i&1:
            piv|=1<<i; v=p[i+1];p[i+1]=0
            if b:p[0]^=v
            for j in bits(a^(1<<i)):p[j+1]^=v
        else:out.append((a,b))
    free=dead&~piv
    if free.bit_count()>=2:return None
    if free:p=[p[free.bit_length()]]+[0]*n
    B=plain(out);p=norm(B,p)
    return (B,p) if any(p) else None

def add(T,B,P):
    P=norm(B,P);V=tuple(a^b for a,b in zip(T.get(B,(0,)*len(P)),P))
    if any(V):T[B]=V
    elif B in T:del T[B]

def coface(A,P,B,Q):
    # Parallel siblings: same homogeneous rows, differing RHS; same tangent slopes.
    if tuple(a for a,b in A)==tuple(a for a,b in B) and A!=B and P[1:]==Q[1:]:
        j=next(i for i,((a,b),(c,d)) in enumerate(zip(A,B)) if b!=d)
        a,b=A[j]; rows=[]
        for i,((u,v),(w,z)) in enumerate(zip(A,B)):
            if i==j:continue
            rows.append((u^a,v^b) if v!=z else (u,v))
        H=plain(rows); delta=P[0]^Q[0];R=list(P)
        if b:R[0]^=delta
        for i in bits(a):R[i+1]^=delta
        return H,norm(H,R), 'siblings'
    # Nested: parent and one hyperplane, equal restrictions on child.
    if len(A)>len(B): A,P,B,Q=B,Q,A,P
    if len(B)==len(A)+1 and plain(A+B)==B and norm(B,P)==Q:
        a,b=next((a,b) for a,b in B if plain(A+((a,b),))!=A)
        H=plain(A+((a,b^1),))
        return H,norm(H,P),'nested'
    return None

def simplify(S,stats):
    while True:
        found=False
        for A,B in combinations(list(S),2):
            r=coface(A,S[A],B,S[B])
            if r is None:continue
            H,P,kind=r;del S[A];del S[B];add(S,H,P);stats[kind]+=1;found=True;break
        if not found:return S

def violate(c):return tuple((1<<(abs(l)-1),int(l<0)) for l in c)
def sat(x,f):return all(any(bool(x>>(abs(l)-1)&1)==(l>0) for l in c) for c in f)
def contract(n,rows,f,merge=True,cap=100000):
    B=plain(rows);active=(1<<n)-1;suffix=[0]*(len(f)+1);stats=Counter()
    for j in range(len(f)-1,-1,-1):
        suffix[j]=suffix[j+1]
        for l in f[j]:suffix[j]|=1<<(abs(l)-1)
    P=(1,)+tuple(1<<(i+1) for i in range(n))
    item=project(B,P,active,suffix[0]);active=suffix[0]
    S={} if item is None else {item[0]:item[1]};peak=len(S);raw=peak
    for j,c in enumerate(f):
        T={}
        for B,P in S.items():
            for R in (B,plain(B+violate(c))):
                item=project(R,P,active,suffix[j+1])
                if item is not None:add(T,*item)
        raw=max(raw,len(T));S=simplify(T,stats) if merge else T
        active=suffix[j+1];peak=max(peak,len(S))
        if len(S)>cap:return None,peak,raw,stats
    assert set(S)<={ () }
    return S.get((),(0,))[0],peak,raw,stats

def value(B,P,x):
    if any((a&x).bit_count()%2!=b for a,b in B):return 0
    v=P[0]
    for i in bits(x):v^=P[i+1]
    return v

def reference(n,rows,f):
    p=0;count=0
    for x in range(1<<n):
        if sat(x,f) and all((a&x).bit_count()%2==b for a,b in rows):p^=1|(x<<1);count+=1
    return p,count

def main():
    rng=Random(89);total=Counter()
    for n in range(1,8):
        for _ in range(100):
            A=plain(tuple((rng.randrange(1<<n),0) for _ in range(rng.randrange(n))))
            if len(A)==n:continue
            a=next(i for i in range(1<<n) if plain(A+((i,0),))!=A)
            B=plain(A+((a,0),));C=plain(A+((a,1),));P=tuple(rng.randrange(1<<(n+1)) for _ in range(n+1))
            Q=norm(B,P);R=list(norm(C,P));R[0]^=rng.randrange(1<<(n+1));R=tuple(R)
            for X,U,Y,V in [(B,Q,C,R),(A,norm(A,P),B,Q)]:
                H,W,k=coface(X,U,Y,V)
                assert all(value(X,U,x)^value(Y,V,x)==value(H,W,x) for x in range(1<<n))
                total[k]+=1
    for n in range(0,9):
        for _ in range(70):
            rows=tuple((rng.randrange(1<<n),rng.randrange(2)) for _ in range(rng.randrange(n+1)))
            f=[tuple(rng.choice((-1,1))*i for i in rng.sample(range(1,n+1),rng.randrange(min(n,3)+1))) for _ in range(rng.randrange(9))]
            p,c=reference(n,rows,f);a,peak,raw,st=contract(n,rows,f);b,*_=contract(n,rows,f,False)
            assert p==a==b;total['cnf']+=1;total['singleton']+=c==1;total['actual_merges']+=sum(st.values())
    # All variables remain live through delayed nontrivial cycle implications.
    for n in (2,4,8,12,16,32,64,128):
        f=[(-i,) for i in range(1,n+1)]+[(-i,i%n+1) for i in range(1,n+1)]
        a,peak,raw,st=contract(n,(),f,cap=2);assert a==1 and peak==1 and raw<=2
        if n<=12:
            b,old,_,_=contract(n,(),f,False,cap=1<<n);assert b==1 and old>=1<<n
        print('live',n,'old_prefix',1<<n,'new_peak',peak,'raw',raw,'merges',sum(st.values()))
    # Pair-rewrite incompleteness: three lines in F2^2, same constant packet.
    S={((1,0),):(1,0,0),((2,0),):(1,0,0),((3,0),):(1,0,0)}
    assert len(simplify(S,Counter()))==3
    assert all(sum(value(B,P,x) for B,P in S.items())%2==1 for x in range(4))
    x,y=sp.symbols('x y');assert sp.Poly((1+x)+(1+y)+(1+x+y)-1,x,y,modulus=2).is_zero
    print(dict(total))
if __name__=='__main__':main()
