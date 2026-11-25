#!/usr/bin/env python3
"""Source-indexed Griess C13/26, typed Levi wheel, Y443 paths and FRACTRAN.
Griess/Sah, classical Singer incidence, Conway FRACTRAN, JMD path words;
new DASHI finite attachment. Not a Monster, analytic j or physical theorem.
"""
from itertools import product, combinations
from collections import Counter
from fractions import Fraction as F
import sympy as s

def require(ok, label):
    if not ok:
        raise RuntimeError(label)

M=s.Matrix([[1,1,0],[0,1,1],[1,1,1]])
I=s.eye(3); G=-M; r=(1,1,1)
def mod(A): return A.applyfunc(lambda x:int(x)%3)
def bal(v): return tuple((int(x)+1)%3-1 for x in v)
def act(A,v): return bal(A*s.Matrix(v))
def dot(v,w): return sum(a*b for a,b in zip(v,w))
def neg(v): return tuple(-x for x in v)
def canon(v): return min(v,neg(v))
N=M.inv_mod(3).T
require(mod(M**13)==I and mod(G**13)==mod(-I) and mod(M.T*N)==I,'source matrices')
P=[act(M**i,r) for i in range(13)]; L=[act(N**i,r) for i in range(13)]
require(len(set(map(canon,P)))==len(set(map(canon,L)))==13,'Singer orbits')
D={i for i,p in enumerate(P) if dot(p,r)%3==0}
require(D=={0,6,10,11},'source offsets')
require(Counter((a-b)%13 for a in D for b in D if a!=b)==Counter(range(1,13)),'difference set')
B=s.Matrix(13,13,lambda i,j:int(dot(P[i],L[j])%3==0)); J=s.ones(13)
require(all(B[i,j]==int((i-j)%13 in D) for i,j in product(range(13),repeat=2)),'circulant')
require(B*B.T==B.T*B==3*s.eye(13)+J,'incidence Gram')
Bi=B.T/3-J/12
require(B*Bi==Bi*B==s.eye(13),'incidence inverse')
V=list(product(range(2),range(13)))
E={(i,j) for i,j in product(range(13),repeat=2) if B[i,j]}
T=lambda v:(v[0],(v[1]+1)%13)
R=lambda v:(1-v[0],(-v[1])%13)
def edge(v,w): return v[0]!=w[0] and B[(v if v[0]==0 else w)[1],(w if v[0]==0 else v)[1]]==1
require(all(edge(v,w)==edge(T(v),T(w))==edge(R(v),R(w)) for v,w in product(V,repeat=2)),'Levi actions')
require(all(R(T(R(v)))==(v[0],(v[1]-1)%13) for v in V),'dihedral law')
require(len({(b,i) for b,i in V})==26 and len(E)==52,'typed counts')
require(not any({(a-d)%13 for d in D}==D for a in range(13)),'no commuting type swap')
# All signed nonzero field states; coherent gauge, not canonical Axis13 section.
X=[act(G**k,r) for k in range(26)]
require(len(set(X))==26,'signed orbit')
encode={v:(k%2,k%13) for k,v in enumerate(X)}; decode={c:v for v,c in encode.items()}
require(len(decode)==26,'codec')
require(all(encode[act(M,v)]==T(encode[v]) and encode[X[(13-k)%26]]==R(encode[v]) for k,v in enumerate(X)),'spatial lift')
require(sum(edge(v,w)!=edge((1-v[0],v[1]),(1-w[0],w[1])) for v,w in product(V,repeat=2))>0,'antipode not duality')
# Explicit previous Y443 witness, types alternate with depth.
raw=[(0,r),(1,(1,0,-1)),(0,(1,0,1)),(1,(1,-1,-1)),(0,(0,1,-1)),(1,(0,1,-1)),(0,(0,1,1)),(1,(1,-1,1)),(0,(1,0,-1)),(1,(1,-1,0)),(0,(0,0,1)),(1,(1,1,0))]
idx=[{canon(v):i for i,v in enumerate(S)} for S in (P,L)]
w=[(b,idx[b][canon(v)]) for b,v in raw]
Y={(0,1),(1,2),(2,3),(3,4),(0,5),(5,6),(6,7),(7,8),(0,9),(9,10),(10,11)}
paths=[(11,10,9,0,1,2,3,4),(5,6,7,8),(0,5,6,7,8)]
images=set()
for b,k in V:
    m=tuple((v[0],(v[1]+k)%13) for v in (list(map(R,w)) if b else w))
    images.add(m)
    require(len(set(m))==12 and all(edge(m[i],m[j])==((i,j) in Y) for i,j in combinations(range(12),2)),'Y443 induced')
    require(all(edge(m[p[i]],m[p[j]])==(j-i==1) for p in paths for i,j in combinations(range(len(p)),2)),'JMD paths')
    require(all(not edge(m[4],m[i]) for i in paths[1]),'JMD beta nonedges')
require(len(images)==26,'Y443 transport orbit')
# New FRACTRAN program, not the old terminating FractranCOL program.
forward=(F(2,3),F(3**12,2**12)); backward=(F(3,2),F(2**12,3**12))
def step(n,prog):
    for f in prog:
        x=n*f
        if x.denominator==1: return x.numerator
    return None
def code(v):
    b,i=v; return 2**i*3**(12-i)*(5 if b==0 else 7)
require(len(set(map(code,V)))==26 and step(1,forward)==step(1,backward)==None,'origin and codec')
for v in V:
    n=code(v); require(step(n,forward)==code(T(v)),'FRACTRAN forward')
    require(step(step(n,forward),backward)==n,'FRACTRAN inverse')
    z=n
    for _ in range(13): z=step(z,forward)
    require(z==n,'13 period')
    require(code(R(v))==step(code((1-v[0],12-v[1])),forward),'polarity bank exchange')
# Actual signed exponent deltas on the original ordered SSP prime list.
primes=(2,3,5,7,11,13,17,19,23,29,31,41,47,59,71)
def valuation(n):
    out=[]
    for p in primes:
        k=0
        while n%p==0:
            k+=1; n//=p
        out.append(k)
    require(n==1,'SSP factor support')
    return tuple(out)
def delta(n,m): return tuple(b-a for a,b in zip(valuation(n),valuation(m)))
changes=[delta(code(v),step(code(v),prog)) for v in V for prog in (forward,backward)]
require(Counter(changes)==Counter({(1,-1)+(0,)*13:24,(-1,1)+(0,)*13:24,(-12,12)+(0,)*13:2,(12,-12)+(0,)*13:2}),'signed valuation transitions')
require(all(tuple(sum(x!=0 for x in d[k:k+5]) for k in (0,5,10))==(2,0,0) for d in changes),'chosen delta support lens bank collision')
for v in V:
    for prog in (forward,backward):
        n=code(v); m=step(n,prog); d=delta(n,m)
        q=F(1)
        for p,k in zip(primes,d): q*=F(p)**k
        require(q==F(m,n),'signed delta exact fraction')
print('PASS 52 SSP signed transition reconstructions; bank and coarse-sign collisions')
print('PASS D',sorted(D),'52 flags; 169 incidence comparisons; inverse B^T/3-J/12')
print('PASS 676 paired action checks; D13 vs antipode; real incidence carry',Counter(dot(P[i],L[j])//3 for i,j in E))
print('PASS 26 transported Y443 witnesses, 1716 induced pair comparisons; original JMD paths')
print('PASS 26 FRACTRAN forward/inverse/13-step/polarity cases, retained origin')
