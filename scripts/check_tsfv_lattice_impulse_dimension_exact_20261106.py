#!/usr/bin/env python3
"""Exact local retarded-impulse early-time coefficients on a CHOSEN
three-dimensional nearest-neighbour oscillator lattice, N=5.

Genuine source kick/readout test for this specific model, not original
TSVF observational data and not universal emergent 3+1. At finite
lattice spacing there is NO exact compact causal light cone.
"""
from fractions import Fraction as F
from itertools import combinations, product

N = 5
c = F(3,2)
a = F(1,5)
mu = F(7,10)
c2a2 = c*c/(a*a)
origin = (0,0,0)


def neighbours(x):
    for j in range(3):
        for sign in (-1,1):
            y=list(x)
            y[j]=(y[j]+sign)%N
            yield tuple(y)


def wave_stiffness(state):
    result={}
    for x in product(range(N),repeat=3):
        source=state.get(x,F(0))
        value=(mu*mu+6*c2a2)*source-c2a2*sum(
            state.get(y,F(0)) for y in neighbours(x))
        if value:
            result[x]=value
    return result


def check():
    kick={origin:F(1)}  # initial velocity; initial position zero
    stiffness1=wave_stiffness(kick)
    stiffness2=wave_stiffness(stiffness1)
    near=set(neighbours(origin))
    assert len(near)==6
    assert stiffness1[origin]==mu*mu+6*c2a2
    assert all(stiffness1[x]==-c2a2 for x in near)
    assert set(stiffness1)==near|{origin}
    # Exact retarded Taylor:
    # sin(t sqrt(L))/sqrt(L) δ0 = tδ0 - t^3 Lδ0/6
    #                             + t^5 L²δ0/120 +...
    third_order={x:-v/F(6) for x,v in stiffness1.items()}
    assert all(third_order[x]==c2a2/F(6) for x in near)
    # Infer the 3 pairs of opposite local spatial directions from the
    # observed near-field graph, not from a prewritten (3,1) mask.
    opposite=[]
    transverse=[]
    for u,v in combinations(sorted(near),2):
        common=set(neighbours(u))&set(neighbours(v))
        assert origin in common
        if len(common)==1:
            opposite.append((u,v))
        elif len(common)==2:
            transverse.append((u,v))
        else:
            raise AssertionError((u,v,common))
    assert len(opposite)==3
    assert len(transverse)==12
    assert len({v for pair in opposite for v in pair})==6
    # A non-neighbour has first nonzero t^5 coefficient; do not claim
    # a compactly supported exact finite-spacing retarded light cone.
    second_shell=set(
        y for x in near for y in neighbours(x)
    )-(near|{origin})
    assert len(second_shell)==18
    assert all(stiffness1.get(x,F(0))==0 for x in second_shell)
    assert all(stiffness2.get(x,F(0))!=0 for x in second_shell)
    print("PASS exact chosen-source local impulse: 125 lattice sites")
    print("6 earliest nonzero offsite channels; t^3 coefficient",c2a2/F(6))
    print("3 opposite spatial channel pairs; 12 transverse pairs")
    print("18 nonzero farther t^5 responses; no exact finite-a light cone")
    print("SCOPE chosen Z_N^3; physical original TSVF and universal 4D OPEN")


if __name__ == "__main__":
    check()
