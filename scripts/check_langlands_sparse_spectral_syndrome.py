"""Bounded-support spectral syndrome recovery. Exhaustive producer is TEST ONLY."""
from itertools import combinations, product
from random import Random
import sympy as sp

class Field:
    def __init__(self,n):
        h=1
        while 2*h<n+1: h*=3
        self.m=2*h; self.mod=(1<<self.m)|(1<<h)|1; self.mask=(1<<self.m)-1
    def mul(self,a,b):
        c=0
        while b:
            if b&1:c^=a
            b>>=1;a<<=1
            if a>>self.m:a^=self.mod
        return c
    def pow(self,a,e):
        c=1
        while e:
            if e&1:c=self.mul(c,a)
            a=self.mul(a,a);e>>=1
        return c
    def inv(self,a):
        if not a: raise ZeroDivisionError
        return self.pow(a,(1<<self.m)-2)
    def trim(self,p):
        p=list(p)
        while p and not p[-1]:p.pop()
        return p
    def add(self,a,b):return self.trim([(a[i] if i<len(a) else 0)^(b[i] if i<len(b) else 0) for i in range(max(len(a),len(b)))])
    def pmul(self,a,b):
        if not a or not b:return []
        c=[0]*(len(a)+len(b)-1)
        for i,x in enumerate(a):
            for j,y in enumerate(b):c[i+j]^=self.mul(x,y)
        return self.trim(c)
    def divmod(self,a,b):
        a=self.trim(a);b=self.trim(b)
        if not b:raise ZeroDivisionError
        q=[0]*max(0,len(a)-len(b)+1);iv=self.inv(b[-1])
        while len(a)>=len(b):
            d=len(a)-len(b);v=self.mul(a[-1],iv);q[d]=v
            for i,x in enumerate(b):a[d+i]^=self.mul(x,v)
            a=self.trim(a)
        return self.trim(q),a
    def rem(self,a,b):return self.divmod(a,b)[1]
    def gcd(self,a,b):
        while b:a,b=b,self.rem(a,b)
        return [self.mul(x,self.inv(a[-1])) for x in a] if a else []
    def solve(self,A,b):
        r=len(b); a=[list(row)+[v] for row,v in zip(A,b)]
        for j in range(r):
            i=next((i for i in range(j,r) if a[i][j]),None)
            if i is None:return None
            a[i],a[j]=a[j],a[i];iv=self.inv(a[j][j]);a[j]=[self.mul(x,iv) for x in a[j]]
            for i in range(r):
                if i!=j and a[i][j]:
                    v=a[i][j];a[i]=[x^self.mul(v,y) for x,y in zip(a[i],a[j])]
        return [row[-1] for row in a]
    def roots(self,p):
        # Split by all field-linear trace coordinates; no enumeration of field elements.
        parts=[p]
        for i in range(self.m):
            nxt=[]
            for f in parts:
                if len(f)<=2:nxt.append(f);continue
                u=self.rem([0,1<<i],f); tr=[]
                for _ in range(self.m):
                    tr=self.add(tr,u);u=self.rem(self.pmul(u,u),f)
                g=self.gcd(f,tr)
                if 1<len(g)<len(f):
                    q,rem=self.divmod(f,g);assert not rem;nxt.extend((g,q))
                else:nxt.append(f)
            parts=nxt
        if any(len(f)!=2 for f in parts):return None
        return [self.mul(f[0],self.inv(f[1])) for f in parts]

def syndrome(F,ids,k):
    s=[0]*(2*k)
    for a in ids:
        v=1
        for j in range(2*k):s[j]^=v;v=F.mul(v,a)
    return s

def recover(F,s,k,n,verify):
    # Largest invertible leading Hankel block. Empty and failure both UNKNOWN.
    for r in range(k,0,-1):
        c=F.solve([[s[i+j] for j in range(r)] for i in range(r)],s[r:2*r])
        if c is None:continue
        roots=F.roots(c+[1])
        if roots is None or len(set(roots))!=r:return None
        if any(not (1<=a<=1<<n) or not verify(a-1) for a in roots):return None
        if syndrome(F,roots,k)!=s:return None
        return sorted(a-1 for a in roots)
    return None

def main():
    rng=Random(369);x=sp.Symbol('x'); fields=0
    for n in (0,1,2,5,6,8,17,18,32,54):
        F=Field(n);h=F.m//2
        assert sp.Poly(x**(2*h)+x**h+1,x,modulus=2).is_irreducible;fields+=1
    supports=0;off=0;cnfs=0;large=0
    for n in range(1,4):
        F=Field(n);k=min(3,1<<n)
        for mask in range(1<<(1<<n)):
            ids=[a+1 for a in range(1<<n) if mask>>a&1]
            v=recover(F,syndrome(F,ids,k),k,n,lambda a: bool(mask>>a&1))
            if 0<len(ids)<=k:assert v==[a-1 for a in ids];supports+=1
            else:
                assert v is None or all(mask>>a&1 for a in v);off+=1
    for n in range(1,8):
        F=Field(n);k=4
        for _ in range(40):
            f=[[(i,rng.randrange(2)) for i in rng.sample(range(n),rng.randint(1,min(3,n)))] for _ in range(rng.randrange(0,4*n+1))]
            sat=lambda a:all(any((a>>i&1)==b for i,b in c) for c in f)
            ids=[a+1 for a in range(1<<n) if sat(a)]
            v=recover(F,syndrome(F,ids,k),k,n,sat)
            if 0<len(ids)<=k:assert v==[a-1 for a in ids]
            else:assert v is None or all(sat(a) for a in v)
            cnfs+=1
    for n in (16,32,64,128):
        F=Field(n)
        for k in (1,2,4,6):
            ids=sorted({rng.randrange(1,1<<n) for _ in range(k)})
            v=recover(F,syndrome(F,ids,k),k,n,lambda a:a+1 in ids)
            assert v==[a-1 for a in ids];large+=1
    # Explicit zero syndrome on inhabited affine subspace: sum all a^j=0 for j<7 in GF8.
    F=Field(4) # GF64, use affine 3-dimensional binary subspace in GF64.
    assert syndrome(F,list(range(8,16)),2)==[0]*4
    print(dict(irreducible_fields=fields,bounded_supports=supports,off_promise_controls=off,cnfs=cnfs,large_roundtrips=large,occupied_zero=1))
if __name__=='__main__':main()
