"""Scoped exact controls for Section 19, not native kernel acceptance."""
from collections import Counter
from itertools import product
from random import Random
from fractions import Fraction as F
import sympy as s
from check_pnp_paid_exterior_search import paid_exterior_search
from check_pnp_conditional_autarky import accepts
if not __debug__: raise SystemExit('assertions required')
C=Counter(); rng=Random(36919)
def check(lane, ok):
    assert ok,lane
    C[lane]+=1
# PNP: exhaustive reference for both completed and refused exterior searches.
for n in range(1,8):
    for _ in range(32):
        clauses=tuple(tuple((1 if rng.randrange(2) else -1)*(i+1) for i in rng.sample(range(n),rng.randrange(min(4,n)+1))) for _ in range(rng.randrange(7)))
        rows=tuple(tuple(rng.randrange(3) for _ in range(n)) for _ in range(rng.randrange(3)))
        target=tuple(rng.randrange(3) for _ in rows)
        want=[x for x in product((0,1),repeat=n) if accepts(clauses,x) and tuple(sum(a*b for a,b in zip(row,x))%3 for row in rows)==target]
        for cap,trial,width,m in ((10**7,10000,n,n),(50000,5000,2,n),(500,200,2,1),(0,200,2,1)):
            status,x,paid,attempts=paid_exterior_search(clauses,n,rows,target,cap,trial,m,width)
            check('PNP',0<=paid<=cap and attempts*trial<=paid)
            check('PNP',status=='UNKNOWN' or (status=='WITNESS' and x in want) or (status=='EMPTY' and not want and x is None))
            if cap==10**7: check('PNP',status!='UNKNOWN')
# BSD: symbolic tangent and actual doubling coordinate identities.
x,r,t,u=s.symbols('x r t u'); a,b,c=x-r*r,x-t*t,x-u*u
X=x+r*t+t*u+u*r; Y=-(r+t)*(t+u)*(u+r); m=-(r+t+u)
a2=-(a+b+c); a4=a*b+b*c+c*a
check('BSD',s.expand(3*X**2+2*a2*X+a4-2*Y*m)==0)
check('BSD',s.expand(m*m-a2-2*X-x)==0)
check('BSD',s.expand(-Y-m*(x-X)+r*t*u)==0)
# Hodge: multiplication by homogenizing indeterminate injective even in Z/m.
for mod in range(2,25):
    for _ in range(24):
        p=[rng.randrange(mod) for _ in range(9)]
        n=rng.randrange(1,9); shifted=[0]*n+p
        check('Hodge',(not any(shifted))==(not any(p)))
# NS: ordered complex convection conjugation, exact Gaussian rational arithmetic.
I=s.I
def dot(k,u):return sum(a*b for a,b in zip(k,u))
def rhs(k,q,u,v):
    w=[dot(q,u)*z for z in v]; mass=dot(k,k); d=dot(k,w)
    return tuple(s.expand(-I*(z-(F(a,mass)*d if mass else 0))) for a,z in zip(k,w))
for _ in range(128):
    k=tuple(rng.randrange(-2,3) for _ in range(3)); q=tuple(rng.randrange(-2,3) for _ in range(3))
    u=tuple(rng.randrange(-3,4)+I*rng.randrange(-3,4) for _ in range(3));v=tuple(rng.randrange(-3,4)+I*rng.randrange(-3,4) for _ in range(3))
    got=rhs(tuple(-a for a in k),tuple(-a for a in q),tuple(s.conjugate(z) for z in u),tuple(s.conjugate(z) for z in v))
    check('NS',got==tuple(s.conjugate(z) for z in rhs(k,q,u,v)))
# YM: noncommuting dual-number product versus explicit insertion sum.
def qm(a,b):
    w,x,y,z=a; t,u,v,h=b
    return (w*t-x*u-y*v-z*h,w*u+x*t+y*h-z*v,w*v-x*h+y*t+z*u,w*h+x*v-y*u+z*t)
def add(a,b):return tuple(x+y for x,y in zip(a,b))
def prod(qs):
    z=(1,0,0,0)
    for q in qs:z=qm(z,q)
    return z
for _ in range(128):
    qs=[tuple(rng.randrange(-3,4) for _ in range(4)) for _ in range(rng.randrange(1,9))]
    ds=[tuple(rng.randrange(-3,4) for _ in range(4)) for q in qs]
    value=(1,0,0,0); d=(0,0,0,0)
    for q,h in zip(qs,ds):d,value=add(qm(d,q),qm(value,h)),qm(value,q)
    want=(0,0,0,0)
    for i,h in enumerate(ds):want=add(want,prod(qs[:i]+[h]+qs[i+1:]))
    check('YM',d==want and value==prod(qs))
print(dict(C),'TOTAL',sum(C.values()),'PASS')
