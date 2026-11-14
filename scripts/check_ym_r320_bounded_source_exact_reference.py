#!/usr/bin/env python3
"""Exact rational bounded-source R320 regression; not a physical SU(N)/Agda proof."""
from fractions import Fraction as Q
from random import Random
import json

def coefficients(weights, first, second):
    assert len(weights) == len(first) == len(second) and weights
    assert all(w > 0 for w in weights)
    assert all(0 <= v <= 2 for v in first + second)
    return (
        sum(weights, Q(0)),
        sum((w*f for w,f in zip(weights,first)), Q(0)),
        sum((w*g for w,g in zip(weights,second)), Q(0)),
        sum((w*f*g for w,f,g in zip(weights,first,second)), Q(0)),
    )

def mixed_log(coefs):
    z, zs, zt, zst = coefs
    return (z*zst-zs*zt)/(z*z)

def covariance(weights, first, second):
    z = sum(weights, Q(0))
    ef = sum((w*f for w,f in zip(weights,first)), Q(0))/z
    eg = sum((w*g for w,g in zip(weights,second)), Q(0))/z
    return sum((w*(f-ef)*(g-eg) for w,f,g in zip(weights,first,second)), Q(0))/z

def run(seed=20261106, trials=25000):
    rng = Random(seed)
    for _ in range(trials):
        n = rng.randrange(1,13)
        w = [Q(rng.randrange(1,19),rng.randrange(1,11)) for _ in range(n)]
        f = [Q(rng.randrange(0,21),10) for _ in range(n)]
        g = [Q(rng.randrange(0,21),10) for _ in range(n)]
        lhs=mixed_log(coefficients(w,f,g))
        assert lhs == covariance(w,f,g)
        assert abs(lhs) <= 1
    w=[Q(1),Q(1)]
    assert mixed_log(coefficients(w,[Q(0),Q(2)],[Q(0),Q(2)])) == 1
    assert mixed_log(coefficients(w,[Q(0),Q(2)],[Q(2),Q(0)])) == -1
    return {"seed":seed,"rational_cases":trials,
            "same_source_covariance":"PASS","uniform_abs_bound":"PASS",
            "perfect_correlation_negative_control":"PASS",
            "scope":"finite rational reference, not Agda/Haar/CMP116/OS"}

if __name__ == "__main__":
    print(json.dumps(run(),indent=2,sort_keys=True))
