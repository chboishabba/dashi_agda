#!/usr/bin/env python3
"""Exact integer SU(2) Wilson mixed vertices on original side-four torus.
P33 pure-quaternion coordinates, six oriented plaquettes, positive link
starts x,x+mu,x+nu,x and signs +,+,-,-. Fourier convention i^(p.x).
Returns 24 times mixed derivatives of sum(1-Re quaternion plaquette),
without continuum, gauge-fixed constrained propagator or beta claims.
"""
from itertools import product, permutations, combinations
from math import factorial
from functools import lru_cache
from collections import defaultdict

L=4
SITES=list(product(range(L),repeat=4))
PLANES=list(combinations(range(4),2))
ZERO=(0,0); ONE=(1,0)
PHASE=(ONE,(0,1),(-1,0),(0,-1))
def add(a,b): return (a[0]+b[0],a[1]+b[1])
def mul(a,b): return (a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0])
def scale(a,n): return (a[0]*n,a[1]*n)
def shift(x,mu): return tuple((v+(j==mu))%L for j,v in enumerate(x))
def phase(p,x): return PHASE[sum(a*b for a,b in zip(p,x))%L]
def color_mul(a,b):
    if a==0:return 1,b
    if b==0:return 1,a
    if a==b:return -1,0
    return (1 if (a,b) in ((1,2),(2,3),(3,1)) else -1),6-a-b
@lru_cache(None)
def sym_color(colors):
    # Symmetrized derivative of exp(sum t_i e_i) multiplied by m!.
    acc=[0]*4
    for order in permutations(colors):
        sign,axis=1,0
        for c in order:
            s,axis=color_mul(axis,c);sign*=s
        acc[axis]+=sign
    return tuple(acc)
def slot_coords(x,mu,nu):
    return ((x,mu,1),(shift(x,mu),nu,1),(shift(x,nu),mu,-1),(x,nu,-1))
def scalar_color_product(vectors):
    state=[1,0,0,0]
    for v in vectors:
        nxt=[0]*4
        for a,b in product(range(4),repeat=2):
            s,c=color_mul(a,b);nxt[c]+=s*state[a]*v[b]
        state=nxt
    return state[0]
def terms(legs,mu,nu):
    # For each allocation of labelled derivatives to the four ordered links,
    # each slot receives the symmetrized noncommutative exponential derivative.
    axes=(mu,nu,mu,nu); signs=(1,1,-1,-1)
    for where in product(range(4), repeat=len(legs)):
        if any(legs[j][0]!=axes[s] for j,s in enumerate(where)):continue
        groups=[[j for j,s in enumerate(where) if s==a] for a in range(4)]
        vectors=[sym_color(tuple(legs[j][1] for j in g)) for g in groups]
        denom=1;sgn=1
        for s,g in enumerate(groups):denom*=factorial(len(g));sgn*=signs[s]**len(g)
        # product factorial divides r! and hence 24 for r<=4.
        assert 24%denom==0
        coeff=-sgn*(24//denom)*scalar_color_product(vectors)
        if coeff:yield where,coeff
def vertex_fourier(legs):
    if any(sum(p[i] for _,_,p in legs)%L for i in range(4)):return ZERO
    ans=ZERO
    x=(0,0,0,0)
    for mu,nu in PLANES:
        slots=slot_coords(x,mu,nu)
        for where,c in terms(legs,mu,nu):
            z=ONE
            for (_,_,p),s in zip(legs,where):z=mul(z,phase(p,slots[s][0]))
            ans=add(ans,scale(z,c*L**4))
    return ans

def vertex_coordinate(legs):
    ans=ZERO
    # Direct truncated polynomial in distinct nilpotent labels. Independent
    # of the allocations/vertex formula: construct each exponential by repeated
    # polynomial quaternion multiplication and sum powers / m!.
    r=len(legs); full=(1<<r)-1
    def pmul(A,B):
        out=defaultdict(lambda:ZERO)
        for (mask,a),v in A.items():
            for (mask2,b),w in B.items():
                if mask&mask2:continue
                s,c=color_mul(a,b);key=(mask|mask2,c)
                out[key]=add(out[key],scale(mul(v,w),s))
        return {k:v for k,v in out.items() if v!=ZERO}
    # Each slot's coefficient is multiplied by 24; the final product is
    # divided by 24^3 to recover a single common derivative scaling.
    for x in SITES:
        for mu,nu in PLANES:
            poly={(0,0):ONE}
            for site,axis,sign in slot_coords(x,mu,nu):
                A={(1<<j,color):scale(phase(p,site),sign)
                   for j,(a,color,p) in enumerate(legs) if a==axis}
                power={(0,0):ONE}; exp=defaultdict(lambda:ZERO)
                for m in range(r+1):
                    for key,v in power.items():exp[key]=add(exp[key],scale(v,24//factorial(m)))
                    power=pmul(power,A)
                    if not power:break
                poly=pmul(poly,exp)
            ans=add(ans,scale(poly.get((full,0),ZERO),-1))
    assert all(v%24**3==0 for v in ans)
    return tuple(v//24**3 for v in ans)

def main():
    p=(1,0,0,0);q=(0,1,0,0);z=(0,0,0,0);neg=lambda p:tuple(-a%4 for a in p)
    close=lambda *ps:tuple(-sum(p[i] for p in ps)%4 for i in range(4))
    cases=[[(1,1,p),(1,1,neg(p))],
           [(0,1,p),(1,2,q),(1,3,close(p,q))],
           [(0,1,z),(1,2,z),(0,1,z),(1,2,z)],
           [(0,1,p),(1,2,q),(0,1,neg(p)),(1,2,neg(q))],
           [(0,1,p),(1,2,q),(0,1,z),(1,2,z)],
           [(1,1,p),(1,1,p),(1,1,neg(p)),(1,1,neg(p))]]
    for legs in cases:
        a=vertex_fourier(legs);b=vertex_coordinate(legs)
        assert a==b,(legs,a,b)
        assert all(vertex_fourier(tuple(legs[j] for j in perm))==a for perm in permutations(range(len(legs))))
        print(f'order={len(legs)} vertex*24={a}; coordinate/Fourier exact match')
    # Constant commutator: deficit = 2 sin²(s) sin²(t), mixed s,s,t,t = 8 per site.
    assert vertex_fourier(cases[2])==(24*8*L**4,0)
    # Free transverse two-jet at p=(pi/2,0,0,0): D(p)=2.
    assert vertex_fourier(cases[0])==(24*2*L**4,0)
    assert vertex_fourier(cases[4])==ZERO
    print('PASS exact P33 Wilson two/three/four-jet Fourier attachment on 6 selected mode sets and all leg permutations')
    print('OPEN constrained gauge/FP loop contractions, continuum normalization, four physical beta integrals')
if __name__=='__main__':main()
