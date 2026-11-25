"""Capped primal/dual spectral producer; reference enumeration is tests only."""
from itertools import product
from random import Random

class Exhausted(Exception): pass
class Budget:
    def __init__(self, cap): self.left = cap
    def pay(self, n=1):
        self.left -= n
        if self.left < 0: raise Exhausted

class Field:
    def __init__(self, n):
        h=1
        while 2*h<n+1: h*=3
        self.m=2*h; self.mod=(1<<self.m)|(1<<h)|1
    def mul(self,a,b):
        z=0
        while b:
            if b&1:z^=a
            b>>=1;a<<=1
            if a>>self.m:a^=self.mod
        return z

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

def affine_chart(n,B):
    piv={a.bit_length()-1:(a,b) for a,b in B}
    base=sum(b<<i for i,(a,b) in piv.items())
    directions=[(1<<j)^sum(((a>>j)&1)<<i for i,(a,b) in piv.items()) for j in range(n) if j not in piv]
    return base,directions

def affine_moments(K,n,B,J,budget):
    """Affine label a=2^n XOR x; j=0,...,J-1. No large-fibre enumeration."""
    budget.pay(n+J+len(B))
    d=n-len(B)
    if (1<<d)>J:return [0]*J
    base,V=affine_chart(n,B);out=[0]*J
    X=[base^(1<<n)]
    for v in V:X += [x^v for x in X]
    for a in X:
        p=1
        for j in range(J):
            budget.pay();out[j]^=p;p=K.mul(p,a)
    return out

def mul(A,B,budget):
    out=set()
    for a in A:
        for b in B:budget.pay();out.symmetric_difference_update((a|b,))
    return out

def suffix_anf(f,budget):
    out={0}
    for c in reversed(f):
        bad={0}
        for l in c:
            b=1<<(abs(l)-1);bad=mul(bad,{0,b} if l>0 else {b},budget)
        bad.symmetric_difference_update((0,));out=mul(out,bad,budget)
    return out

def sat(x,f,rows):
    return all(any(bool(x>>(abs(l)-1)&1)==(l>0) for l in c) for c in f) and all((a&x).bit_count()%2==b for a,b in rows)

def join(n,rows,f,cut,J,budget):
    K=Field(n);budget.pay(n+len(rows)+len(f)+sum(map(len,f))+J)
    B=canon(rows);S=set() if B is None else {B}
    for c in f[:cut]:
        T=set(S);bad=tuple((1<<(abs(l)-1),int(l<0)) for l in c)
        for B in S:
            budget.pay();R=canon(B+bad)
            if R is not None:T.symmetric_difference_update((R,))
        S=T
    A=suffix_anf(f[cut:],budget);out=[0]*J
    for B in S:
        for mask in A:
            budget.pay();R=canon(B+tuple((1<<i,1) for i in range(n) if mask>>i&1))
            if R is not None:
                v=affine_moments(K,n,R,J,budget);out=[a^b for a,b in zip(out,v)]
    return out

def observe(n,rows,f,levels,cap):
    """First nonzero exact prefix, or UNKNOWN. Every attempt has a charged share."""
    per=cap//max(1,len(levels)*(len(f)+1))
    for J in levels:
        for cut in sorted(range(len(f)+1),key=lambda j:abs(2*j-len(f))):
            try:v=join(n,rows,f,cut,J,Budget(per))
            except Exhausted:continue
            if any(v):return v
            break
    return None

def recover(n,rows,f,levels,cap):
    v=observe(n,rows,f,levels,cap//2)
    if v is None:return None
    # Keep one nonzero syndrome coordinate; one child suffices by additivity.
    j=next(j for j,x in enumerate(v) if x);value=v[j];x=0;pins=tuple(rows)
    per=cap//(2*max(1,n)*(len(f)+1))
    for i in range(n):
        for cut in sorted(range(len(f)+1),key=lambda j:abs(2*j-len(f))):
            try:q=join(n,pins+((1<<i,0),),f,cut,j+1,Budget(per))[j]
            except Exhausted:continue
            break
        else:return None
        b=int(q==0)
        if not b:value=q
        assert value
        x|=b<<i;pins+=((1<<i,b),)
    return x if sat(x,f,rows) else None

def reference(n,rows,f,J):
    K=Field(n);out=[0]*J
    for x in range(1<<n):
        if sat(x,f,rows):
            p=1
            for j in range(J):out[j]^=p;p=K.mul(p,(1<<n)^x)
    return out

def main():
    from sympy import Symbol, Poly
    z=Symbol('z');rng=Random(369);charts=joins=observations=recovered=0
    for n in range(9):
        K=Field(n);h=K.m//2
        assert Poly(z**(2*h)+z**h+1,z,modulus=2).is_irreducible
        for _ in range(40):
            rows=tuple((rng.randrange(1<<n),rng.randrange(2)) for _ in range(rng.randrange(n+1)))
            B=canon(rows);J=rng.randrange(1,17)
            if B is not None:
                assert affine_moments(K,n,B,J,Budget(100000))==reference(n,rows,[],J);charts+=1
            f=[tuple(rng.choice((-1,1))*i for i in rng.sample(range(1,n+1),rng.randrange(min(3,n)+1))) for _ in range(rng.randrange(7))]
            want=reference(n,rows,f,J)
            for cut in range(len(f)+1):
                assert join(n,rows,f,cut,J,Budget(100000))==want;joins+=1
            v=observe(n,rows,f,[1,2,4,8,16],1000000)
            if v is not None:assert any(v) and v==reference(n,rows,f,len(v));observations+=1
            x=recover(n,rows,f,[1,2,4,8,16],2000000)
            if v is not None:assert x is not None and sat(x,f,rows)
            if x is not None:recovered+=1
    for n in (32,64,128,256):
        assert join(n,(),[],0,16,Budget(1000))==[0]*16
        assert observe(n,(),[],[1,2,4,8,16],10000) is None
        f=[(i,) for i in range(1,n+1)]
        v=join(n,(),f,0,4,Budget(10000));K=Field(n);a=(1<<(n+1))-1
        assert v==[1,a,K.mul(a,a),K.mul(K.mul(a,a),a)]
    # Eight models are invisible to the first seven syndromes, not the eighth.
    assert join(3,(),[],0,7,Budget(1000))==[0]*7
    assert join(3,(),[],0,8,Budget(1000))[-1]!=0
    assert observe(3,(),[],[1,2,4,8],0) is None
    assert recover(3,(),[],[1,2,4,8],100000) in range(8)
    print(dict(fields=9,affine_charts=charts,cut_comparisons=joins,nonzero_observations=observations,verified_recoveries=recovered,large_controls=8,blindness_and_exhaustion='PASS'))
if __name__=='__main__':main()
