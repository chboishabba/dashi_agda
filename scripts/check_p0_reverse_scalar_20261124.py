"""G131+: actual factor-elimination DAG and division-free reverse marginals."""
from itertools import product
from random import Random
from sympy import symbols, expand, diff

def field_mul(a,b):
    c=0
    while b:
        if b&1:c^=a
        b>>=1;a<<=1
        if a&32:a^=37 # X^5+X^2+1
    return c

class DAG:
    def __init__(self,mod):
        self.mod=mod; self.v=[]; self.ops=[]
    def addval(self,a,b):return a^b if self.mod==32 else (a+b)%self.mod
    def mulval(self,a,b):return field_mul(a,b) if self.mod==32 else a*b%self.mod
    def leaf(self,v):
        self.v.append(v);self.ops.append(None);return len(self.v)-1
    def gate(self,op,a,b):
        self.v.append((self.addval if op=='+' else self.mulval)(self.v[a],self.v[b]));self.ops.append((op,a,b));return len(self.v)-1
    def backward(self,out):
        d=[0]*len(self.v);d[out]=1
        for k in range(len(d)-1,-1,-1):
            if self.ops[k] is None:continue
            op,a,b=self.ops[k]
            da,db=(d[k],d[k]) if op=='+' else (self.mulval(d[k],self.v[b]),self.mulval(d[k],self.v[a]))
            d[a]=self.addval(d[a],da);d[b]=self.addval(d[b],db)
        return d

def contract(n,F,weights,mod,pins=()):
    g=DAG(mod);zero=g.leaf(0);one=g.leaf(1)
    ids=[[g.leaf(v) for v in w] for w in weights]
    fs=[((i,),{(b,):ids[i][b] for b in (0,1)}) for i in range(n)]
    for clause in F+tuple((i+1 if b else -i-1,) for i,b in pins):
        scope=tuple(sorted({abs(l)-1 for l in clause}));tab={}
        for bits in product((0,1),repeat=len(scope)):
            a=dict(zip(scope,bits));tab[bits]=one if any(a[abs(l)-1]==int(l>0) for l in clause) else zero
        fs.append((scope,tab))
    width=0
    for i in range(n):
        picked=[(s,t) for s,t in fs if i in s];fs=[(s,t) for s,t in fs if i not in s]
        scope=tuple(sorted(set().union(*(set(s) for s,t in picked))));width=max(width,len(scope));rem=tuple(j for j in scope if j!=i);tab={}
        for bits in product((0,1),repeat=len(rem)):
            a=dict(zip(rem,bits));terms=[]
            for b in (0,1):
                a[i]=b;v=one
                for s,t in picked:v=g.gate('*',v,t[tuple(a[j] for j in s)])
                terms.append(v)
            tab[bits]=g.gate('+',*terms)
        fs.append((rem,tab))
    out=one
    for s,t in fs:
        assert not s;out=g.gate('*',out,t[()])
    d=g.backward(out)
    marg=[[g.mulval(g.v[k],d[k]) for k in row] for row in ids]
    return g.v[out],marg,width,sum(op is not None for op in g.ops)

def brute(n,F,w,mod,pins=()):
    g=DAG(mod);z=0;m=[[0,0] for _ in range(n)]
    for x in product((0,1),repeat=n):
        if any(x[i]!=b for i,b in pins) or not all(any(x[abs(l)-1]==int(l>0) for l in c) for c in F):continue
        v=1
        for i,b in enumerate(x):v=g.mulval(v,w[i][b])
        z=g.addval(z,v)
        for i,b in enumerate(x):m[i][b]=g.addval(m[i][b],v)
    return z,m

rng=Random(369);cases=marginals=pinned=shannon=0
for mod in (8,32):
    for n in range(1,7):
        for _ in range(20):
            F=tuple(tuple(rng.choice((-1,1))*i for i in rng.sample(range(1,n+1),rng.randint(1,min(3,n)))) for j in range(rng.randrange(9)))
            w=[[rng.randrange(mod),rng.randrange(mod)] for _ in range(n)]
            z,m,_,_=contract(n,F,w,mod);assert (z,m)==brute(n,F,w,mod);cases+=1;marginals+=2*n
            for i in range(n):
                assert DAG(mod).addval(*m[i])==z;shannon+=1
                for b in (0,1):
                    assert contract(n,F,w,mod,((i,b),))[0]==m[i][b];pinned+=1
print('source cases',cases,'marginals',marginals,'independent pinned comparisons',pinned,'Shannon checks',shannon)
# Cyclic independent-set CNF: compare against transfer trace, no brute expansion.
for n in (12,48,192):
    F=tuple((-i,-(i%n+1)) for i in range(1,n+1));w=[[1,1] for _ in range(n)]
    z,m,width,cost=contract(n,F,w,8)
    a,b,c,d=1,0,0,1
    for _ in range(n):a,b,c,d=(a+b)%8,a,(c+d)%8,c
    assert z==(a+d)%8 and width<=3
    assert all((u+v)%8==z for u,v in m)
    print('cycle',n,'width',width,'forward gates',cost,'scalar mod8',z)
# Neutral support: all weights one, nonempty full 2-bit cube, every marginal zero in GF32.
assert contract(2,(),[[1,1],[1,1]],32)[:2]==(0,[[0,0],[0,0]])
# Nonzero parent and all marginals nonzero, but independently picking zeros violates XOR.
F=((1,2),(-1,-2));z,m,_,_=contract(2,F,[[1,2],[1,3]],32)
assert z!=0 and all(v!=0 for row in m for v in row) and brute(2,F,[[1,2],[1,3]],32,((0,0),(1,0)))[0]==0
# Actual formal identity on symbolic XOR polynomial.
a,b,c,d=symbols('a b c d');Z=a*d+b*c
assert expand(a*diff(Z,a)+b*diff(Z,b)-Z)==0
assert expand(c*diff(Z,c)+d*diff(Z,d)-Z)==0
print('neutral/joint controls 2/2; symbolic identities 2/2')
