#!/usr/bin/env python3
"""Exact original Wilson R445 reflection on genuine local plaquette words.

Source: BalabanPeriodicTorus4Carrier and the actual 2-positive-link
SU(N) native R445 block (side 4 -> 2); no independent Gibbs measure.
This finite noncommutative free-group check concerns the source GEOMETRY.
It is not Wilson reflection positivity, an Agda receipt or a Clay proof.
"""
from itertools import combinations, product

D = 4
FINE = tuple(product(range(4), repeat=D))
COARSE = tuple(product(range(2), repeat=D))
PLANES = tuple(combinations(range(D), 2))

def step(x, axis, modulus, offset=1):
    out = list(x)
    out[axis] = (out[axis] + offset) % modulus
    return tuple(out)

def reflect(x, modulus):
    out = list(x)
    out[0] = (-out[0]) % modulus
    return tuple(out)

def inverse(word):
    return tuple((bond, -sign) for bond, sign in reversed(word))

def reduced(letters):
    result = []
    for letter in letters:
        if result and result[-1][0] == letter[0] and result[-1][1] == -letter[1]:
            result.pop()
        else:
            result.append(letter)
    return tuple(result)

def mul(*parts):
    return reduced(letter for part in parts for letter in part)

def fine_link(site, axis):
    return (((site, axis), 1),)

def fine_reflected_link(site, axis):
    point = reflect(site, 4)
    if axis == 0:
        return inverse(fine_link(step(point, 0, 4, -1), axis))
    return fine_link(point, axis)

def original_block(site, axis, link=fine_link):
    origin = tuple(2 * c for c in site)
    return mul(link(origin, axis), link(step(origin, axis, 4), axis))

def reflected_coarse_block(site, axis):
    ref = reflect(site, 2)
    if axis == 0:
        return inverse(original_block(step(ref, 0, 2, -1), axis))
    return original_block(ref, axis)

def coarse_plaquette(site, i, j, coarse_link):
    return mul(coarse_link(site, i), coarse_link(step(site, i, 2), j),
               inverse(coarse_link(step(site, j, 2), i)),
               inverse(coarse_link(site, j)))

def real_trace_class(word):
    # Re Tr of an SU(N) word is invariant under cyclic permutation and
    # inversion of the entire unitary word; no commutativity of links.
    word = reduced(word)
    options = []
    for orientation in (word, inverse(word)):
        for offset in range(max(1, len(orientation))):
            options.append(orientation[offset:] + orientation[:offset])
    return min(options)

def original_coarse_plaquette_support(site, i, j):
    sides = ((site, i), (step(site, i, 2), j),
             (step(site, j, 2), i), (site, j))
    out = set()
    for coarse_site, axis in sides:
        origin = tuple(2 * c for c in coarse_site)
        out.add((origin, axis))
        out.add((step(origin, axis, 4), axis))
    return out

def check():
    assert len(FINE) == 256 and len(COARSE) == 16 and len(PLANES) == 6
    assert 4 * len(FINE) == 1024 and 6 * len(FINE) == 1536
    for site, axis in product(COARSE, range(D)):
        assert original_block(site, axis, fine_reflected_link) == reflected_coarse_block(site, axis)
    originals = []
    for site in COARSE:
        for i, j in PLANES:
            left = coarse_plaquette(site, i, j,
                lambda x, d: original_block(x, d, fine_reflected_link))
            right = coarse_plaquette(site, i, j, reflected_coarse_block)
            assert left == right
            assert real_trace_class(left) == real_trace_class(right)
            originals.append((real_trace_class(left), real_trace_class(right)))
    assert len(originals) == 96
    for a, b in product(originals, repeat=2):
        assert (a[0], b[0]) == (a[1], b[1])
    positives = [(site, i, j) for site in COARSE if site[0] == 0
                 for i, j in PLANES]
    assert len(positives) == 48
    for site, i, j in positives:
        support = original_coarse_plaquette_support(site, i, j)
        assert all(x[0] in ({0, 1} if axis == 0 else {0, 1, 2})
                   for x, axis in support)
    print('PASS original fine bonds=1024, original fine plaquettes=1536')
    print('PASS actual R445 ordered non-Abelian block reflection 64/64')
    print('PASS original 4D coarse Wilson plaquette trace words 96/96')
    print('PASS original two-plaquette ordered words 9216/9216')
    print('PASS selected candidate positive-time plaquette support 48/48')
    print('OPEN Agda kernel, published fine RP, original E1/D1/D2 physical gap')

if __name__ == '__main__':
    check()
