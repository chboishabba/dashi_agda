#!/usr/bin/env python3
"""Independent exact controls for Section 17; not a Lean/Agda replay."""
from itertools import product
from fractions import Fraction as F
from collections import Counter
import random
import subprocess
import sympy as s

if not __debug__:
    raise SystemExit('assertions required')
counts = Counter()
def check(lane, claim):
    assert claim, lane
    counts[lane] += 1

# BSD actual reverse-half point and root translation on split smooth cubics.
for p in (5,7,11,13,17,19,23,29,31,37,41,43,47):
    roots = (0,1,p-1)
    def add(P,Q):
        if P is None: return Q
        if Q is None: return P
        x,y=P; u,v=Q
        if x==u and (y+v)%p==0: return None
        m=((3*x*x-1)*pow(2*y,-1,p) if x==u else (v-y)*pow(u-x,-1,p))%p
        z=(m*m-x-u)%p
        return z,(m*(x-z)-y)%p
    for x in range(p):
        if x in roots: continue
        rs=[[r for r in range(p) if r*r%p==(x-e)%p] for e in roots]
        for r,t,u in product(*rs):
            def half(a,b,c): return ((x+a*b+b*c+c*a)%p, (-(a+b)*(b+c)*(c+a))%p)
            Q=half(r,t,u)
            check('BSD',add(Q,Q)==(x,-r*t*u%p))
            for i,signs in enumerate(((1,-1,-1),(-1,1,-1),(-1,-1,1))):
                R=half(*(v*sign for v,sign in zip((r,t,u),signs)))
                check('BSD',R==add(Q,(roots[i],0)))
                check('BSD',add(R,(Q[0],-Q[1]%p))==(roots[i],0))
for row in product((-1,1),repeat=3):
    check('BSD', (row[0]*row[1]*row[2]==1)==(row.count(-1)%2==0))

# Hodge denominator identity, unit equivalence in nonreduced rings.
a,x,v=s.symbols('a x v')
check('Hodge',s.expand((v*v-a)**2-v*v*(x*x-4*a)-(v*v+x*v+a)*(v*v-x*v+a))==0)
for m in (4,8,9,12,16,18,25,27):
    for d in range(m):
        check('Hodge',(s.gcd(d,m)==1)==(s.gcd(d*d,m)==1))
rng=random.Random(1701)
for _ in range(256):
    aa=[F(rng.randrange(-5,6)) for _ in range(6)]
    vv=[F(rng.choice([-3,-2,-1,1,2,3])) for _ in range(6)]
    xx=[w+b/w for b,w in zip(aa,vv)]
    eta=s.prod(vv);delta=F(rng.randrange(-3,4))
    d=eta*delta*s.prod(b*w*(w*w-b) for b,w in zip(aa,vv))
    base=eta**6*delta**2*s.prod(b*b*(z*z-4*b) for b,z in zip(aa,xx))
    check('Hodge',d*d==base)

# NS actual projection including zero mode; weighted tail on one cutoff.
for k in product(range(-2,3),repeat=3):
    mass=sum(a*a for a in k)
    for _ in range(4):
        u=[F(rng.randrange(-9,10),3) for _ in k]
        d=sum(a*b for a,b in zip(k,u))
        P=[b-F(a,mass)*d if mass else b for a,b in zip(k,u)]
        check('NS',sum(a*b for a,b in zip(k,P))==0)
for _ in range(128):
    e=[(sum(a*a for a in k),F(rng.randrange(0,20),7)) for k in product(range(-2,3),repeat=3) if any(k)]
    D=sum(m*w for m,w in e)
    for R in (1,2,3,4):
        check('NS',R*R*sum(w for m,w in e if m>=R*R)<=D)

# Unit quaternion tangent norm and adjoint two-point operator bound.
def qm(a,b):
    w,x,y,z=a; t,u,v,h=b
    return (w*t-x*u-y*v-z*h,w*u+x*t+y*h-z*v,w*v-x*h+y*t+z*u,w*h+x*v-y*u+z*t)
def star(q): return (q[0],*(-x for x in q[1:]))
def sub(a,b): return tuple(x-y for x,y in zip(a,b))
def n2(a): return sum(x*x for x in a)
def unit():
    x,y,z=[F(rng.randrange(-7,8),5) for _ in range(3)]
    d=1+x*x+y*y+z*z
    return ((2-d)/d,2*x/d,2*y/d,2*z/d)
for _ in range(256):
    q,p=unit(),unit(); H=(F(0),*(F(rng.randrange(-9,10),7) for _ in range(3)))
    check('YM',n2(qm(q,H))==n2(H)==n2(qm(H,q)))
    check('YM',qm(star(q),qm(q,H))[0]==0)
    check('YM',n2(sub(qm(qm(q,H),star(q)),qm(qm(p,H),star(p))))<=4*n2(sub(q,p))*n2(H))

# Adaptive transcript: state influences subsequent coordinate choices.
def run(x,start,fuel):
    state=start; trace=[]
    for step in range(fuel):
        i=(state+step)%len(x); trace.append(i)
        state=(state*3+x[i]+1)%17
    return state,trace
for _ in range(256):
    n=9;x=tuple(rng.randrange(2) for _ in range(n)); y=tuple(rng.randrange(2) for _ in range(n))
    start=rng.randrange(17);fuel=rng.randrange(0,10)
    a,R=run(x,start,fuel);b,S=run(y,start,fuel)
    hit=any(x[i]!=y[i] for i in R)
    check('PNP',hit or (a,R)==(b,S))
    check('PNP',a==b or hit)
    z=tuple(x[i] if i in R else rng.randrange(2) for i in range(n))
    check('PNP',run(z,start,fuel)==(a,R))

# RH shell pipefail: a full scan must see hidden paths even in long output.
for hidden in ('S','h','H'):
    cmd="set -o pipefail; (printf '%s first\\n' \"$1\"; for i in {1..20000}; do echo 'H tracked'; done) | grep -E '^([S]|[a-z])' >/dev/null"
    r=subprocess.run(['bash','-c',cmd,'_',hidden],check=False)
    check('RH admission', (r.returncode==0)==(hidden!='H'))
print(dict(counts), 'TOTAL',sum(counts.values()), 'PASS')
