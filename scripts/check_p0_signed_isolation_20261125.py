#!/usr/bin/env python3
"""Exact Singer signed precision, sparse prime isolation, ternary affine isolation.
Finite controls only; no SAT complexity separation. Source wheel: PR #1291.
"""
from itertools import product, combinations
from collections import Counter
from random import Random
import sympy as s
from sympy.matrices.normalforms import smith_normal_form
from sympy.polys.domains import ZZ

def require(ok, msg):
    if not ok: raise AssertionError(msg)

M=s.Matrix([[1,1,0],[0,1,1],[1,1,1]]); r=s.Matrix([1,1,1]); N=M.inv_mod(3).T
P=[(M**i*r).applyfunc(lambda x:int(x)%3) for i in range(13)]
L=[(N**i*r).applyfunc(lambda x:int(x)%3) for i in range(13)]
B=s.Matrix(13,13,lambda i,j:int((P[i].dot(L[j]))%3==0)); J=s.ones(13)
require(B*B.T==3*s.eye(13)+J,'Gram')
require({i for i in range(13) if B[i,0]}=={0,6,10,11},'offsets')
D=smith_normal_form(B,domain=ZZ); diag=[abs(int(D[i,i])) for i in range(13)]
require(diag==[1]*7+[3]*5+[12],'Smith')
Q=B.T.row_join(B.T).col_join(B.T.row_join(-B.T)); R=4*B-J
I=R.row_join(R).col_join(R.row_join(-R))
require(I*Q==24*s.eye(26),'signed lift')
rng=Random(369); precision=sharp=0
for h in range(1,9):
    mod=2**(h+3)
    for _ in range(32):
        c=s.Matrix([rng.randrange(2**(h+5)) for _ in range(26)])
        z=(Q*c).applyfunc(lambda a:int(a)%mod)
        # 24=8*3. Integer divisibility by 8 survives modular reduction.
        raw=I*z; require(all(int(a)%8==0 for a in raw),'divisible')
        recovered=[int(a)//8*pow(3,-1,2**h)%2**h for a in raw]
        require(recovered==[int(a)%2**h for a in c],'precision')
        precision+=1
    c=s.ones(26,1)*2**(h-1)
    require(all(int(a)%2**(h+2)==0 for a in Q*c) and any(int(a)%2**h for a in c),'sharp')
    sharp+=1

# Prime residue isolation; integer encodings injective on the original bit cube.
prime_sets=prime_witnesses=count_checks=0
sets=[(3,[x for x in range(8) if mask>>x&1]) for mask in range(1,256)]
sets += [(16,rng.sample(range(2**16),t)) for t in (1,2,4,8,16) for _ in range(12)]
max_prime_count=max(n*len(S)*(len(S)-1)//2+1 for n,S in sets)
primes=list(s.primerange(2,100000))[:max_prime_count]
require(len(primes)==max_prime_count,'prime budget')
for n,S in sets:
    t=len(S); short=primes[:n*(t-1)+1]; recovered=set()
    for p in short:
        bins={}
        for x in S: bins.setdefault(x%p,[]).append(x)
        recovered.update(v[0] for v in bins.values() if len(v)==1)
    require(recovered==set(S),'every witness isolated'); prime_witnesses+=len(S)
    full=primes[:n*t*(t-1)//2+1]
    require(max(sum(v%2 for v in Counter(x%p for x in S).values()) for p in full)==t,'parity count')
    prime_sets+=1;count_checks+=1

# Toeplitz affine maps h(x)=A*x+b over F3; diagonals indexed i-j+n-1.
# Exhaust all seeds for n=3,k=1,2,3 and all 255 nonempty binary supports.
n=3; xs=list(product((0,1),repeat=n)); affine_pairs=isolations=seed_count=0
buckets={}
for k in (1,2,3):
    q=3**k; hist=Counter(); pair_hist=[Counter() for _ in combinations(xs,2)]
    pairs=list(combinations(range(8),2))
    for seed in product(range(3),repeat=n+2*k-1):
        a,b=seed[:n+k-1],seed[n+k-1:]
        vals=[tuple((sum(a[i-j+n-1]*x[j] for j in range(n))+b[i])%3 for i in range(k)) for x in xs]
        mask=sum(1<<i for i,v in enumerate(vals) if not any(v));hist[mask]+=1;seed_count+=1
        for z,(i,j) in enumerate(pairs): pair_hist[z][(vals[i],vals[j])]+=1
    total=3**(n+2*k-1)
    for ph in pair_hist:
        require(len(ph)==q*q and set(ph.values())=={total//(q*q)},'pairwise independence');affine_pairs+=1
    buckets[k]=hist
for S in range(1,256):
    m=S.bit_count();k=1
    while 3**k<2*m:k+=1
    q=3**k;hist=buckets[k];total=sum(hist.values())
    unique=sum(freq for mask,freq in hist.items() if (mask&S).bit_count()==1)
    require(unique*q*q>=total*m*(q-m+1) and unique*12>=total,'isolation probability');isolations+=1

# Explicit deterministic width<=3 gate compiler for residue/hash constraints.
# Each transition is a fixed table represented by OR of AND of one-hot state
# and input bit; every gate is constrained by equivalence clauses.
class Circuit:
    def __init__(self,n):self.n=n;self.ops=[];self.cnf=[]
    def gate(self,op,*a):
        z=self.n+1+len(self.ops);self.ops.append((op,a))
        if op=='0':self.cnf.append((-z,))
        elif op=='1':self.cnf.append((z,))
        elif op=='!':self.cnf.extend([(-z,-a[0]),(z,a[0])])
        elif op=='&':self.cnf.extend([(-z,a[0]),(-z,a[1]),(z,-a[0],-a[1])])
        elif op=='|':self.cnf.extend([(z,-a[0]),(z,-a[1]),(-z,a[0],a[1])])
        return z
    def fold(self,op,vs,initial):
        z=self.gate(str(initial))
        for v in vs:z=self.gate(op,z,v)
        return z
    def residue(self,p,weights,target,offset=0):
        row=[self.gate(str(int(j==offset))) for j in range(p)]
        for i,w in enumerate(weights,1):
            b=self.gate('!',i)
            row=[self.gate('|',self.gate('&',row[j],b),self.gate('&',row[(j-w)%p],i)) for j in range(p)]
        return row[target]
    def lift(self,x):
        a=[0,*x]
        for op,ids in self.ops:
            v=[a[i] for i in ids]
            a.append(int(op=='1') if op in ('0','1') else 1-v[0] if op=='!' else v[0]&v[1] if op=='&' else v[0]|v[1])
        return a
    def check(self,a,cnf):return all(any(a[abs(i)]==int(i>0) for i in c) for c in cnf)
compiled=0;gate_checks=0
for _ in range(32):
    n=3;S=rng.randrange(1,256);c=Circuit(n);p=rng.choice([2,3,5,7]);target=rng.randrange(p)
    weights=[pow(2,i,p) for i in range(n)];rflag=c.residue(p,weights,target)
    A=[[rng.randrange(3) for j in range(n)] for k in range(2)];b=[rng.randrange(3) for k in range(2)]
    hflag=c.fold('&',[c.residue(3,row,0,off) for row,off in zip(A,b)],1)
    F=[tuple(-i-1 if x>>i&1 else i+1 for i in range(n)) for x in range(8) if not(S>>x&1)]
    for x in product((0,1),repeat=n):
        u=sum(v<<i for i,v in enumerate(x));a=c.lift(x)
        require(c.check(a,c.cnf),'unique deterministic lift')
        for flag,want in [(rflag,u%p==target),(hflag,all((sum(w*v for w,v in zip(row,x))+off)%3==0 for row,off in zip(A,b)))]:
            require(c.check(a,c.cnf+F+[(flag,)])==bool(S>>u&1 and want),'original source projection');compiled+=1
        gate_checks+=len(c.ops)
print(dict(smith=diag,precision=precision,sharp=sharp,prime_sets=prime_sets,prime_witnesses=prime_witnesses,count_checks=count_checks,affine_pairs=affine_pairs,isolations=isolations,seeds=seed_count,compiled=compiled,gate_checks=gate_checks))
