#!/usr/bin/env python3
"""Exact rational regression for bounded original plaquette trace word inequalities.

The analytic Wilson expectation/pressure theorem is in
Docs/physics/YMClayOriginalWilsonFixedWordCollapseAndN1Witness20261109.md.
Tests below verify the deterministic telescoping inequalities, NOT
independent-plaquette integration, continuum limits or the Clay gap.
"""
from fractions import Fraction as Q
from itertools import product

SAMPLE=(-Q(1),-Q(1,2),Q(0),Q(1,2),Q(1))

def checked_word(values):
    w=Q(1)
    for z in values:
        assert -1<=z<=1
        w*=z
    deficit=sum((1-z for z in values),Q(0))
    assert abs(1-w)<=deficit
    assert (1-w)**2<=2*deficit
    return w,deficit

def main():
    tests=0
    for length in range(7):
        for values in product(SAMPLE,repeat=length):
            checked_word(values)
            tests+=1
    assert tests==sum(5**k for k in range(7))
    # Cauchy-Schwarz covariance inequality, exact rational weights,
    # for correlations between overlapping words on ONE common source.
    configurations=list(product(SAMPLE,repeat=2))
    weights=[Q(i+1) for i in range(len(configurations))]
    Z=sum(weights)
    weights=[a/Z for a in weights]
    for i in range(2):
        for j in range(2):
            f=[c[i] for c in configurations]
            g=[c[j] for c in configurations]
            meanf=sum((p*x for p,x in zip(weights,f)),Q(0))
            meang=sum((p*x for p,x in zip(weights,g)),Q(0))
            cov=sum((p*(x-meanf)*(y-meang)
                     for p,x,y in zip(weights,f,g)),Q(0))
            vf=sum((p*(x-meanf)**2 for p,x in zip(weights,f)),Q(0))
            vg=sum((p*(y-meang)**2 for p,y in zip(weights,g)),Q(0))
            assert cov*cov <= vf*vg
            assert vf <= sum((p*(x-1)**2 for p,x in zip(weights,f)),Q(0))
    print(f"PASS: {tests} exact rational plaquette-word telescope/square checks")
    print("PASS: original-style same-measure covariance Cauchy-Schwarz checks")
    print("SOURCE: Wilson original finite Gibbs pressure bound requires analytic proof")
    print("OPEN: E1 convergence, N1 noncollapse, D1 spatial decay, full OS D2")

if __name__=="__main__":
    main()
