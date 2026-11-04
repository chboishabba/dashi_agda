#!/usr/bin/env python3
"""Independent exact Fraction reference for additive global Born-error rate.

A physical theorem must separately bound global correlated Born weight
relative to the independent tensor proxy. This deliberately does not
derive a correlation bound from reduced single-site density matrices.
"""
from fractions import Fraction as Q
from random import Random

def cmul(a,b):
    return (a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0])
def born(a):
    return a[0]*a[0]+a[1]*a[1]
def prod(xs):
    val=(Q(1),Q(0))
    for x in xs: val=cmul(val,x)
    return val

pulses=[(Q(3,5),Q(4,5)),(Q(5,13),Q(12,13)),(Q(7,25),Q(24,25))]
gamma_options=[(Q(1),Q(0)),(Q(0),Q(1)),(Q(1,2),Q(1,2)),(Q(0),Q(0))]

def main():
    both=0
    for seed in range(3200):
        rng=Random(seed)
        k=rng.randrange(0,16)
        cs=[rng.choice(pulses)[0] for _ in range(k)]
        gammas=[rng.choice(gamma_options) for _ in range(rng.randrange(0,5))]
        reference=cmul(prod(gammas),prod([(c,Q(0)) for c in cs]))
        eps=Q(rng.randrange(-5,6),100)
        actual=(reference[0]+eps,reference[1]-eps)
        reference_born=born(reference)
        actual_born=born(actual)
        delta=max(Q(0),actual_born-reference_born)
        both+=delta>0
        assert actual_born<=reference_born+delta
        assert 2**k*reference_born<=1
        assert 2**k*actual_born<=1+2**k*delta
        assert (2**k+1)*actual_born<=1+actual_born+2**k*delta
    assert both>0
    print("PASS: 3200 exact rational correlated-error fixtures")
    print("PASS: global Born error bound and corrected two-channel cross inequality")
    print("REFERENCE ONLY: not Agda or physically proven correlation control")

if __name__=="__main__":
    main()
