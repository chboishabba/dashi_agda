#!/usr/bin/env python3
"""Exact Q8 Wilson plaquette action C3/gauge regression on original 4^4.

Uses a finite nonabelian subgroup of SU(2), NOT actual continuous SU(N)
Haar, Agda kernel, full selected CMP119 E/R/B/V action, or Clay proof.
"""
import random
from itertools import product

SITES = list(product(range(4), repeat=4))
AXES = tuple(range(4))
BONDS = [(x, a) for x in SITES for a in AXES]
Q8 = [(sgn,b) for sgn in (1,-1) for b in range(4)]
TABLE = (((1,0),(1,1),(1,2),(1,3)),
         ((1,1),(-1,0),(1,3),(-1,2)),
         ((1,2),(-1,3),(-1,0)),
         ((1,3),(1,2),(-1,1),(-1,0)))

def mul(x,y):
    s,b=TABLE[x[1]][y[1]]
    return (x[0]*y[0]*s,b)
def inv(x):
    return (x[0] if x[1]==0 else -x[0],x[1])
def mm(*values):
    ans=(1,0)
    for x in values: ans=mul(ans,x)
    return ans
def shift(x,a):
    xs=list(x); xs[a]=(xs[a]+1)%4
    return tuple(xs)
def c3site(x): return x[0],x[3],x[1],x[2]
def c3axis(a): return (0,2,3,1)[a]
def c3field(u):
    return {(x,a):u[(c3site(x),c3axis(a))] for x,a in BONDS}
def gaugetransform(u, g):
    return {(x,a):mm(g[x],u[(x,a)],inv(g[shift(x,a)])) for x,a in BONDS}
def plaquette(u,x,a,b):
    return mm(u[(x,a)],u[(shift(x,a),b)],
              inv(u[(shift(x,b),a)]),inv(u[(x,b)]))
def realtrace(q): return 2*q[0] if q[1]==0 else 0
def action_by_plane(u):
    out={}
    for a in range(4):
        for b in range(a+1,4):
            out[a,b]=sum(2-realtrace(plaquette(u,x,a,b)) for x in SITES)
    return out
def action(u): return sum(action_by_plane(u).values())

def run():
    rng=random.Random(443119)
    anisotropic_witnesses=0
    weighted_orbit_controls=0
    for case in range(32):
        u={bond:rng.choice(Q8) for bond in BONDS}
        assert c3field(c3field(c3field(u)))==u
        rotated=c3field(u)
        old=action(u)
        assert action(rotated)==old,(case,old,action(rotated))
        gauge={x:rng.choice(Q8) for x in SITES}
        assert action(gaugetransform(u,gauge))==old
        weights={(a,b):2*a+3*b+1
                 for a,b in product(range(4),repeat=2) if a<b}
        lhs=sum(weights[k]*v for k,v in action_by_plane(u).items())
        rhs=sum(weights[k]*v for k,v in action_by_plane(rotated).items())
        anisotropic_witnesses+=(lhs!=rhs)
        orbit=[u,c3field(u),c3field(c3field(u))]
        physical_weights=[1+action(state) for state in orbit]
        local_observables=[action_by_plane(state)[(0,1)] for state in orbit]
        assert sum(physical_weights[i]*local_observables[i] for i in range(3)) == sum(
            physical_weights[i]*local_observables[(i+1)%3] for i in range(3))
        bad_weights=[
            1+sum(weights[k]*v for k,v in action_by_plane(state).items())
            for state in orbit]
        weighted_orbit_controls += (
            sum(bad_weights[i]*local_observables[i] for i in range(3)) !=
            sum(bad_weights[i]*local_observables[(i+1)%3] for i in range(3)))
    assert anisotropic_witnesses>=20,anisotropic_witnesses
    assert weighted_orbit_controls>=20,weighted_orbit_controls
    print('PASS: 32 original 4^4 Q8 Wilson C3 tests on 1024 bonds')
    print('PASS: 32 C3-cubed and 32 gauge-action invariances')
    print(f'PASS: {anisotropic_witnesses}/32 anisotropic non-C3 action negatives')
    print(f'PASS: 32 weighted C3 orbit numerators; {weighted_orbit_controls}/32 anisotropic weighted negatives')
    print('REFERENCE ONLY: not continuous SU(N) Haar, full CMP119 or Agda kernel')

if __name__=='__main__':run()
