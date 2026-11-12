#!/usr/bin/env python3
"""Exhaustive index-level R445 candidate codec check, exact integers.

Companion to YMClayR445CanonicalBondPermutationCodecExact.agda.
The ordering matches cartesian(allCyclicIndices 4)^4 x axis and
cartesian(allCyclicIndices 2)^4 x axis x phase. This does not replace
Agda 2.9, source-level Haar Fubini, or any Wilson Gibbs estimate.
"""
from hashlib import sha256
from itertools import product
from random import Random

FINE = tuple((*site, mu) for site in product(range(4), repeat=4) for mu in range(4))
COARSE = tuple((*site, mu) for site in product(range(2), repeat=4) for mu in range(4))

def encode_pair(bond, phase):
    *site, mu = bond
    site = [2 * x for x in site]
    site[mu] += phase
    return (*site, mu)

def decode_selected(bond):
    *site, mu = bond
    if any(x % 2 for axis, x in enumerate(site) if axis != mu):
        return None
    phase = site[mu] % 2
    coarse = tuple(x // 2 for x in site) + (mu,)
    return coarse, phase

def check():
    selected = tuple(encode_pair(c, phase) for c in COARSE for phase in (0, 1))
    selected_set = set(selected)
    residual = tuple(b for b in FINE if b not in selected_set)
    reordered = selected + residual
    original_index = {b:i for i,b in enumerate(FINE)}
    perm = tuple(original_index[b] for b in reordered)
    inverse = [None]*len(FINE)
    for dest, orig in enumerate(perm):
        assert inverse[orig] is None
        inverse[orig] = dest
    assert (len(FINE), len(COARSE), len(selected), len(residual)) == (1024,64,128,896)
    assert len(set(selected)) == 128 and len(set(residual)) == 896
    assert set(selected).isdisjoint(residual) and set(reordered) == set(FINE)
    assert all(decode_selected(encode_pair(c,p)) == (c,p) for c in COARSE for p in (0,1))
    assert all(decode_selected(b) is None for b in residual)
    assert all(encode_pair(*decode_selected(b)) == b for b in selected)
    assert all(inverse[perm[j]] == j for j in range(1024))
    rng = Random(1444)
    for trial in range(20):
        values = tuple(rng.randrange(-10_000, 10_000) for _ in FINE)
        re = tuple(values[j] for j in perm)
        back = tuple(re[inverse[j]] for j in range(1024))
        assert values == back
    digest = sha256(','.join(map(str,perm)).encode()).hexdigest()
    assert digest == '49b954c21ccd1649208074eb5096e5b6b63102313da773fe17e1268b67727ada'
    print('PASS 1024 canonical fine bonds; 64 coarse bonds; 128 unique selected; 896 unique residual')
    print('PASS 1024/1024 exhaustive decoder and inverse permutation; 20 random exact field round-trips')
    print('Canonical bond-index permutation SHA-256:', digest)

if __name__ == '__main__':
    check()
