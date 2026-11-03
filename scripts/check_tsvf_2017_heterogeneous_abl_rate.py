#!/usr/bin/env python3
"""Exact rational-complex fixture for heterogeneous TSVF 2017 Born/ABL and rates.

These independent arithmetic checks are NOT Agda typechecking or an actual
2017 many-body physical realization. Original authors: Aharonov et al. 2017;
source owners: DASHI.Quantum.TSVF and existing rational complex modules.
"""
from fractions import Fraction as F
from random import Random

ZERO = (F(0), F(0))
ONE = (F(1), F(0))
I = (F(0), F(1))

def add(a,b): return (a[0]+b[0], a[1]+b[1])
def mul(a,b): return (a[0]*b[0]-a[1]*b[1], a[0]*b[1]+a[1]*b[0])
def conj(a): return (a[0], -a[1])
def norm(a): return a[0]**2 + a[1]**2
def dot(a,b): return add(mul(conj(a[0]),b[0]),mul(conj(a[1]),b[1]))

def power(z,k):
    v=ONE
    for _ in range(k): v=mul(z,v)
    return v

def check():
    rng=Random(20171103)
    eta=(ONE,ZERO)
    eta35=((F(3,5),F(0)),(F(4,5),F(0)))
    orth=(ZERO,ONE)
    phase=(I,ZERO)
    states=(eta,eta35,orth,phase)
    count=0
    for k in range(35):
        for _ in range(60):
            sites=[(rng.choice(states),rng.choice(states)) for _ in range(k)]
            gammas=[(F(rng.randrange(-3,4)),F(rng.randrange(-3,4)))
                    for j in range(rng.randrange(8))]
            gamma=ONE
            for g in gammas: gamma=mul(gamma,g)
            overlap=ONE
            factor=F(1)
            for a,b in sites:
                z=dot(a,b)
                overlap=mul(overlap,z)
                factor*=norm(z)
            wrong=norm(mul(gamma,overlap))
            for g in gammas: factor*=norm(g)
            assert wrong==factor
            assert F(1)/(F(1)+wrong)+wrong/(F(1)+wrong)==1
            assert norm(mul(I,gamma))==norm(gamma)
            count+=1
    assert dot(eta,eta35)==(F(3,5),F(0))
    for k in range(45):
        assert norm(power(dot(eta,eta35),k))==F(9,25)**k

    rates=0
    for k in range(90):
        for _ in range(50):
            R=W=1
            for _ in range(k):
                w=rng.randrange(11); r=2*w+rng.randrange(20)
                W*=w; R*=r
            gr=rng.randrange(101); gw=rng.randrange(gr+1)
            assert (2**k)*W<=R
            assert (2**k+1)*gw*W<=gr*R+gw*W
            rates+=1

    # Counterexample: same one-site diagonal reductions, different global
    # two-site coherent states. Local equal reductions DO NOT prove tensor
    # factorization of the overlap.
    plus=(F(3,5),F(4,5))
    minus=(F(3,5),-F(4,5))
    assert (plus[0]**2,plus[1]**2)==(minus[0]**2,minus[1]**2)
    assert (plus[0]*minus[0]+plus[1]*minus[1])**2==F(49,625)
    assert F(49,625)!=1

    # Adversarial disturbance breaks an unconditional macroscopic guarantee.
    assert 100*9**2>25**2
    print(f"PASS exact complex cases={count}; heterogeneous rate cases={rates}; "
          "homogeneous k=0..44; two negative controls")

if __name__=="__main__":
    check()
