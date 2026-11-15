#!/usr/bin/env python3
"""Exact Fraction noncommutative weighted Haar pair-fibre disintegration.

REFERENCE ONLY. Q8 is a non-Abelian finite test group, not continuous
Borel SU(N), and these weights are arbitrary, not the selected Wilson
Gibbs action on all 1024 physical bonds. Agda kernel still pending.
"""
from fractions import Fraction as Q
from itertools import product
from random import Random

G = list(product((1, -1), range(4)))
BASE = (
    ((1, 0), (1, 1), (1, 2), (1, 3)),
    ((1, 1), (-1, 0), (1, 3), (-1, 2)),
    ((1, 2), (-1, 3), (-1, 0), (1, 1)),
    ((1, 3), (1, 2), (-1, 1), (-1, 0)),
)
def mul(x, y):
    sign, b = BASE[x[1]][y[1]]
    return (x[0] * y[0] * sign, b)
def inverse(x):
    return (x[0] if x[1] == 0 else -x[0], x[1])
def mean(xs):
    xs = list(xs)
    return sum(xs, Q(0)) / len(xs)
def weighted_fine(weight, observable):
    return mean(weight(u, v) * observable(mul(u, v))
                for u in G for v in G)
def effective_density(weight, w):
    return mean(weight(mul(w, inverse(v)), v) for v in G)
def weighted_coarse(weight, observable):
    return mean(effective_density(weight, w) * observable(w) for w in G)

def run():
    for x in G:
        assert mul(x, inverse(x)) == (1, 0)
        assert mul(inverse(x), x) == (1, 0)
        for v in G:
            assert mul(mul(x, inverse(v)), v) == x
    rng = Random(44517)
    for seed in range(1800):
        # Nonfactorizing positive fine weights and arbitrary signed tests
        weight_map = {(u, v):Q(rng.randrange(1, 22), rng.randrange(1, 15))
                      for u in G for v in G}
        observable_map = {w: Q(rng.randrange(-20, 21), rng.randrange(1, 17))
                          for w in G}
        wt = lambda u, v: weight_map[(u, v)]
        obs = lambda w: observable_map[w]
        lhs = weighted_fine(wt, obs)
        rhs = weighted_coarse(wt, obs)
        assert lhs == rhs, (seed, lhs, rhs)
        z_fine = weighted_fine(wt, lambda _:Q(1))
        z_coarse = weighted_coarse(wt, lambda _:Q(1))
        assert z_fine > 0 and z_coarse > 0 and z_fine == z_coarse
        assert lhs/z_fine == rhs/z_coarse
        assert all(effective_density(wt, w) > 0 for w in G)
        # Sum over a spectator affecting all original U,V weights:
        external = rng.randrange(0, 13)
        spectator_wt = lambda u,v: wt(u,v) * (Q(1) + Q(external + u[1] + v[1], 7))
        assert weighted_fine(spectator_wt, obs) == weighted_coarse(spectator_wt, obs)
    # Non-bare explicit source: the chosen two-link weight is not
    # pushforward of unweighted Haar or a free coarse Wilson density.
    special_u, special_v = (1,1), (1,2)
    w0 = lambda u,v: Q(1) + (Q(3, 2) if (u,v)==(special_u,special_v) else Q(0))
    mass = {w:effective_density(w0,w) for w in G}
    assert mass[mul(special_u,special_v)] == Q(19, 16)
    assert sum(mass.values())/len(mass) == Q(131, 128)
    assert len(set(mass.values())) == 2
    assert weighted_fine(w0, lambda _:Q(1)) == weighted_coarse(w0, lambda _:Q(1))
    assert weighted_fine(w0, lambda _:Q(1) if _ == (1,3) else Q(0)) != Q(1,8)
    print("PASS: 1800 exact Q8 weighted fibre-disintegration, partition, normalized and positivity cases")
    print("PASS: 1800 nonfactorizing spectator-dependent weight cases")
    print("PASS: selected nonuniform effective coarse density rejects bare-Haar promotion")
    print("REFERENCE ONLY: Agda kernel, physical SU(N) Haar/weighted Wilson block & UV/IR open")

if __name__ == "__main__":
    run()
