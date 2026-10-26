#!/usr/bin/env python3
"""Source-gated exact Grover output / readout model.

This is an *ideal* finite algorithm with an explicit, caller-supplied
classical readout channel, not a fit to SAXON Q measurements.
Grover: L. K. Grover, STOC 1996.
Experimental interpretation: Gemsheim et al., arXiv:2609.13022 (2026).
Adaptation: Johl Brown and OpenAI assistant (2026-10-26).
"""
from fractions import Fraction as F

def ideal_distribution(marked: frozenset[int], iterations: int, size: int = 8):
    assert size > 0 and 0 < len(marked) <= size and iterations >= 0
    v = [F(1)] * size  # amplitudes scaled by sqrt(size)
    for _ in range(iterations):
        v = [-x if i in marked else x for i, x in enumerate(v)]
        mean = sum(v) / size
        v = [2 * mean - x for x in v]
    return tuple(x*x/size for x in v)

def apply_readout(true_probabilities, channel):
    """channel[reported][true], column stochastic, any dimension."""
    n = len(true_probabilities)
    assert len(channel) == n and all(len(row) == n for row in channel)
    assert all(x >= 0 for x in true_probabilities)
    assert sum(true_probabilities) == 1
    assert all(channel[i][j] >= 0 for i in range(n) for j in range(n))
    assert all(sum(channel[i][j] for i in range(n)) == 1 for j in range(n))
    out = tuple(sum(channel[i][j]*true_probabilities[j] for j in range(n))
                for i in range(n))
    assert sum(out) == 1
    return out

def marked_success(distribution, marked):
    return sum((distribution[i] for i in marked), F(0))

def check():
    I = tuple(tuple(F(i == j) for j in range(8)) for i in range(8))
    for m, rounds, expected in [(1,2,F(121,128)), (2,1,F(1))]:
        from itertools import combinations
        for marked_tuple in combinations(range(8),m):
            marked = frozenset(marked_tuple)
            ideal = ideal_distribution(marked,rounds)
            assert sum(ideal) == 1
            assert marked_success(ideal,marked) == expected
            assert apply_readout(ideal,I) == ideal
    # Non-identity stochastic channel: correct exact normalization and
    # altered observed success. Synthetic only, NOT fitted instrument data.
    confusion = [[F(0) for _ in range(8)] for _ in range(8)]
    for source in range(8):
        confusion[source][source] = F(9,10)
        confusion[(source+1)%8][source] = F(1,10)
    ideal=ideal_distribution(frozenset({0}),2)
    observed=apply_readout(ideal,confusion)
    assert sum(observed)==1
    assert observed != ideal
    assert marked_success(observed,{0}) != marked_success(ideal,{0})
    print("PASS: 36 ideal oracles, identity-channel preservation, synthetic confusion counterexample")

if __name__ == "__main__":
    check()
