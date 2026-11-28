#!/usr/bin/env python3
"""Section 18 scoped exact controls. Native theorem replay is separate."""
from itertools import product
from collections import Counter
from random import Random
import sympy as s
from check_pnp_source_cluster_planner import planned_cluster_join
from check_pnp_conditional_autarky import accepts

if not __debug__:
    raise SystemExit('assertions required')
C=Counter(); rng=Random(36918)
def check(lane,p):
    assert p, lane
    C[lane]+=1

# Original source planner: arbitrary clauses, exterior assignment and F3 rows.
for n in range(1,9):
    for _ in range(48):
        E={i for i in range(n) if rng.randrange(3)==0}
        F=tuple(tuple((1 if rng.randrange(2) else -1)*(i+1) for i in rng.sample(range(n),rng.randrange(min(3,n)+1))) for j in range(rng.randrange(7)))
        x=tuple(rng.randrange(2) for i in range(n))
        rows=tuple(tuple(rng.randrange(3) for i in range(n)) for j in range(rng.randrange(3)))
        t=tuple(rng.randrange(3) for row in rows)
        want=[y for y in product((0,1),repeat=n) if all(x[i]==y[i] for i in E) and accepts(F,y) and tuple(sum(a*b for a,b in zip(row,y))%3 for row in rows)==t]
        out=planned_cluster_join(F,n,E,x,rows,t,10**8,width=n)
        check('PNP',out is not None and out[0]==len(want))
        check('PNP',out[1] in want if want else out[1] is None)
        check('PNP',0<=out[2]<=10**8)
        check('PNP',planned_cluster_join(F,n,E,x,rows,t,0,width=n) is None)
        check('PNP',planned_cluster_join(F,n,E,x,rows,t,out[2],width=n)==out)
# A connected clause across the requested boundary must not be falsely split.
check('PNP',planned_cluster_join(((1,2,3,4,5),),5,(),(0,)*5,(),(),10**8,width=4) is None)
check('PNP',planned_cluster_join(((1,),),2,(0,),(0,0),(),(),1000)==(0,None,1+9+4))

# Hodge: localization kills exactly d-power torsion, including nonreduced rings.
# In Z/m, localization at d removes the prime powers dividing d.
for m in range(2,65):
    for d in range(m):
        retained=m
        while (g:=int(s.gcd(retained,d)))>1: retained//=g
        killed={a for a in range(m) if a%retained==0}
        # m successive powers more than suffice for a finite m-element ring.
        dn=pow(d,m,m); d2n=pow(d,2*m,m)
        check('Hodge',killed=={a for a in range(m) if dn*a%m==0})
        check('Hodge',killed=={a for a in range(m) if d2n*a%m==0})

# BSD actual split cubic reverse half and cyclic sign address.
for p in (5,7,11,13,17,19,23,29,31):
    roots=(0,1,p-1)
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
        rs=[[a for a in range(p) if a*a%p==(x-e)%p] for e in roots]
        for a,b,c in product(*rs):
            def half(r,t,u): return ((x+r*t+t*u+u*r)%p, (-(r+t)*(t+u)*(u+r))%p)
            Q=half(a,b,c)
            check('BSD',half(b,c,a)==Q==half(c,a,b))
            for i,signs in enumerate(((1,-1,-1),(-1,1,-1),(-1,-1,1))):
                R=half(*(v*sg for v,sg in zip((a,b,c),signs)))
                check('BSD',add(R,(Q[0],-Q[1]%p))==(roots[i],0))

# NS scalar integrating-factor cancellation and nonzero real damping factor.
t,a,b,c=s.symbols('t a b c',real=True)
f=(b+s.I*c)*s.exp(-a*t)
check('NS',s.simplify(s.diff(f,t)+a*f)==0)
check('NS',s.simplify(s.diff(s.exp(a*t)*f,t))==0)
check('NS',s.simplify(s.exp(a*t)*f-f.subs(t,0))==0)
# YM actual signed bond derivative at zero, with both multiplication orders.
q=s.symbols('q0:4',real=True); H=(0,*s.symbols('h1:4',real=True))
def qm(a,b):
    w,x,y,z=a; t,u,v,h=b
    return (w*t-x*u-y*v-z*h,w*u+x*t+y*h-z*v,w*v-x*h+y*t+z*u,w*h+x*v-y*u+z*t)
def star(a): return (a[0],*(-x for x in a[1:]))
# First-order Taylor jet of exp(tH); exact coefficient, not numerical derivative.
for sign in (1,-1):
    jet=(1,*(sign*t*h for h in H[1:]))
    curve=qm(q,jet) if sign==1 else qm(jet,star(q))
    expected=qm(q,H) if sign==1 else tuple(-x for x in qm(H,star(q)))
    for got,want in zip(curve,expected):
        check('YM',s.expand(s.diff(got,t)-want)==0)
print(dict(C),'TOTAL',sum(C.values()),'PASS')
