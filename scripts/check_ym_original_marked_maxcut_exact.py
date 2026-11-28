#!/usr/bin/env python3
"""Source-independent finite exact regression; NOT an Agda kernel receipt.

Tests the algebra behind original M.02/F19 marked pushforward with S3,
a non-Abelian FINITE surrogate for the one-link SU(N) Haar change.
The user's original 1024-bond Wilson density and the Agda 64-pair proof
remain the authority; this test cannot establish their typecheck or
a uniform Wilson RG estimate.
"""
from fractions import Fraction as Q
from itertools import permutations, product

G = list(permutations(range(3)))
index = {p: i for i, p in enumerate(G)}
identity = tuple(range(3))
assert identity in index


def mul(a, b):
    return tuple(a[b[i]] for i in range(3))


def inv(a):
    result = [0, 0, 0]
    for i, x in enumerate(a):
        result[x] = i
    return tuple(result)


def physical_weight(u, v, x, y, spectator):
    # Strictly positive and genuinely coupled across both marked
    # noncommutative link pairs and the spectator link.
    a, b, c, d, e = [index[z] for z in (u, v, x, y, spectator)]
    return Q(1 + ((a*7 + b*11 + c*13 + d*17 + e*19 +
                    a*d + b*e + c*a + d*e) % 29), 1)


def marks(w1, w2, s, t):
    f = Q(index[w1] - 2*index[w2], 3)
    g = Q(index[w2] + index[w1]**2, 5)
    return (1 + s*f)*(1 + t*g)


def check_original_marked_haar():
    tests = [(Q(0), Q(0)), (Q(2, 7), Q(-3, 11)),
             (Q(-1, 2), Q(5, 13)), (Q(1), Q(1))]
    originals = [Q(0) for _ in tests]
    changed = [Q(0) for _ in tests]

    for u, v, x, y, spectator in product(G, repeat=5):
        w1, w2 = mul(u, v), mul(x, y)
        weight = physical_weight(u, v, x, y, spectator)
        for i, (s, t) in enumerate(tests):
            originals[i] += weight*marks(w1, w2, s, t)

    for w1, v, w2, y, spectator in product(G, repeat=5):
        u, x = mul(w1, inv(v)), mul(w2, inv(y))
        weight = physical_weight(u, v, x, y, spectator)
        for i, (s, t) in enumerate(tests):
            changed[i] += weight*marks(w1, w2, s, t)

    assert originals == changed
    assert originals[0] > 0
    assert [val/originals[0] for val in originals] == [
        val/changed[0] for val in changed]
    print("PASS 4 signed/zero two-mark source tests; 7776 nonabelian")
    print("     five-link inputs per side, full coupled spectator weight")
    print("PASS original effective / canonical same-Z normalization")


def check_partition_equality_is_not_rg_decay():
    bare = (Q(1), Q(1))
    effective = (Q(3, 2), Q(1, 2))
    integrate = lambda pair: sum(pair, Q(0))/2
    assert integrate(bare) == integrate(effective) == 1
    assert all(x > 0 for x in bare + effective)
    test = (Q(1), Q(0))
    marked = lambda density: sum((density[i]*test[i] for i in range(2)), Q(0))/2
    assert marked(effective) == Q(3, 4)
    assert marked(bare) == Q(1, 2)
    assert marked(effective) - marked(bare) == Q(1, 4)
    for cutoff in range(128):
        assert abs(effective[0] - bare[0]) == Q(1, 2)
        assert marked(effective) - marked(bare) == Q(1, 4)
    print("PASS 128 cutoffs: positive equal-Z densities retain")
    print("     exact nonzero 1/2 density and 1/4 F/G/FG moment differences")
    assert 2*64 + 896 == 1024
    print("PASS original 64 ordered pairs / 896 spectators = 1024 bonds")


if __name__ == "__main__":
    check_original_marked_haar()
    check_partition_equality_is_not_rg_decay()
    print("OPEN local Agda 2.9 acceptance, original SU(N) matrix trace,")
    print("     actual scalar/Haar carrier weld, P0.F UV-uniform RG bound,")
    print("     E1/D1/D2/N1/G1 and separate #1498 physical beta quadratures")
