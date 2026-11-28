#!/usr/bin/env python3
"""Finite H05 incidence history consumer; exact rational execution, no CI/kernel.
Source Griess/Sah matrix, Singer incidence, Conway FRACTRAN, existing DASHI
wheel checker and H05. JMD source path/SSP motivation upstream, not a new theorem.
"""
from itertools import product, permutations
from collections import Counter
from fractions import Fraction as F
from dataclasses import dataclass, replace
import sympy as s

def require(ok, label):
    if not ok: raise RuntimeError(label)

M=s.Matrix([[1,1,0],[0,1,1],[1,1,1]])
r=s.Matrix([1,1,1]); N=M.inv_mod(3).T
bal=lambda a: tuple((int(v)+1)%3-1 for v in a)
P=[bal(M**i*r) for i in range(13)]; L=[bal(N**i*r) for i in range(13)]
dot=lambda v,w: sum(a*b for a,b in zip(v,w))
D=tuple(i for i in range(13) if dot(P[i],L[0])%3==0)
require(D==(0,6,10,11),'source offsets')
pairs={(e-d)%13:(d,e) for d,e in product(D,repeat=2) if d!=e}
require(len(pairs)==12,'unique moving path')
primes=(2,3,5,7,11,13,17,19,23,29,31,41,47,59,71)
forward=(F(2,3),F(3**12,2**12)); backward=(F(3,2),F(2**12,3**12))

def code(b,i): return (5 if b==0 else 7)*2**i*3**(12-i)
def val(n):
    result=[]
    for p in primes:
        k=0
        while n%p==0: n//=p; k+=1
        result.append(k)
    require(n==1,'full SSP factorization'); return tuple(result)
def short(k): return (k+6)%13-6

def endpoint(src):
    if src is None: return None
    b,i,d,e=src; a=1 if b==0 else -1
    j=(i-a*d)%13; k=(j+a*e)%13
    pi,li=(i,j) if b==0 else (j,i)
    pj,lj=(k,j) if b==0 else (j,k)
    carries=(dot(P[pi],L[li])//3,dot(P[pj],L[lj])//3)
    require(dot(P[pi],L[li])%3==dot(P[pj],L[lj])%3==0,'actual incidence')
    return b,i,j,k,carries

def compact(src):
    if src is None: return None
    b,i,d,e=src; delta=(e-d)%13
    return b,i,delta,d if delta==0 else None

def expand(obs):
    if obs is None: return None
    b,i,delta,tag=obs
    d,e=(tag,tag) if delta==0 else pairs[delta]
    return b,i,d,e

# Source command selection independent of geometric endpoint arithmetic.
def execute(src):
    if src is None: return (1,(),(0,)*15)
    b,i,d,e=src; a=1 if b==0 else -1
    cmds=[]
    for k,role in ((-a*d,b),(a*e,1-b)):
        # For the second leg the role switch is at the end as on the first.
        t=short(k); cmds.extend([('F' if t>0 else 'W',forward if t>0 else backward)]*abs(t))
        cmds.append(('P>L' if role==0 else 'L>P',(F(7,5) if role==0 else F(5,7),)))
    n=code(b,i); begin=n; hist=[]
    for name,prog in cmds:
        applicable=next(((j,f) for j,f in enumerate(prog) if (n*f).denominator==1),None)
        require(applicable is not None,'first enabled'); j,f=applicable
        m=(n*f).numerator; vv=tuple(y-x for x,y in zip(val(n),val(m)))
        mult=F(1)
        for p,k in zip(primes,vv): mult*=F(p)**k
        require(mult==f,'signed prime reconstruction')
        hist.append((name,j,n,m,vv)); n=m
    net=tuple(y-x for x,y in zip(val(begin),val(n)))
    return n,tuple(hist),net

def move(src):
    if src is None: return None
    b,i,d,e=src; return b,(i+1)%13,d,e

def polarity(src):
    if src is None: return None
    b,i,d,e=src; return 1-b,(-i)%13,d,e

@dataclass(frozen=True)
class State:
    source: object
    index: tuple
    geometry: object=None
    arithmetic: object=None
    x: bool=False
    y: bool=False
    z: bool=False

def x(q):
    require(not q.x,'axis x used twice')
    return replace(q,geometry=(compact(q.source),endpoint(q.source)),x=True)
def y(q):
    require(not q.y,'axis y used twice')
    src=expand(q.geometry[0]) if q.x else q.source
    return replace(q,arithmetic=execute(src),y=True)
def z(q):
    require(not q.z,'axis z used twice')
    src=move(q.source)
    return replace(q,source=src,z=True,
                   geometry=(compact(src),endpoint(src)) if q.x else None,
                   arithmetic=execute(src) if q.y else None)

def path(q,order):
    for c in order: q={'x':x,'y':y,'z':z}[c](q)
    return q

sources=[None]+list(product(range(2),range(13),D,D))
require(len(sources)==417,'source size')
# One actual finite index per source; indices are independent metadata, not
# identified with wheel position or the order of evaluation of a diagram.
face_count=path_count=0; bad_naive=0; all_net_zero=0
for j,src in enumerate(sources):
    q=State(src,(('prior-history',j),j+10,3,2,1,'full-command-consumer'))
    require(expand(compact(src))==src,'minimal geometry codec reverse')
    a=execute(src)
    if src is not None:
        b,i,mid,k,carries=endpoint(src)
        require(a[0]==code(b,k),'independent arithmetic endpoint')
        switches=[v[3] for v in a[1] if v[0] in ('P>L','L>P')]
        require(switches==[code(1-b,mid),code(b,k)],'independent intermediate flag')
        rev=(b,k,src[3],src[2]); require(execute(rev)[0]==code(b,i),'reverse path')
        if not any(a[2]): all_net_zero+=1
        # Translation is a state-dependent recompile, not a fixed fraction list.
        bad_naive+=tuple(v[4] for v in a[1])!=tuple(v[4] for v in execute(move(src))[1])
        p=polarity(src); ep=endpoint(p)
        require(ep[:4]==(1-b,(-i)%13,(-mid)%13,(-k)%13),'polarity transport')
    for u,v,w in (('x','y','z'),('x','z','y'),('y','z','x')):
        for pre in ('',w):
            a0=path(q,pre+u+v); a1=path(q,pre+v+u)
            require(a0==a1,'six face '+pre+u+v); face_count+=1
    target=path(q,'xyz')
    for order in permutations('xyz'):
        got=path(q,order); require(got==target,'endpoint '+''.join(order)); path_count+=1
        require(got.index==q.index and expand(got.geometry[0])==move(src),'indexed recovery')
    if src is not None: require(move(src)!=src,'nonidentity z')
require(all_net_zero==104,'zero delta retains trace')
require(bad_naive>0,'negative control stale trace')
# Minimal residual for consumer full source among endpoint collisions.
fibres=Counter((b,i,endpoint((b,i,d,e))[3]) for b,i,d,e in sources[1:])
require(Counter(fibres.values())==Counter({1:312,4:26}),'endpoint fibre sizes')
require(len(set(map(compact,sources)))==417,'injective refined code')
print('PASS',face_count,'six-face comparisons;',path_count,'endpoint paths; 416 nonidentity moves + origin')
print('PASS 416 independent arithmetic endpoint/intermediate checks and reverse; 104 zero-net paths')
print('PASS 312 unique moving endpoint fibres, 26 four-way returning fibres; minimal conditional 2 bits')
print('PASS stale signed trace differs on',bad_naive,'translated paths; metadata and source recovered')
