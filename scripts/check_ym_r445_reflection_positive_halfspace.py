#!/usr/bin/env python3
"""Original Wilson side4->side2 native-link reflection and half-space test.

Source: BalabanPeriodicTorus4Carrier and original R445 ordered two-link
block. Both fine reflection t->-t and t->2-t commute algebraically, but
only the former keeps the selected coarse T=0 time-oriented plaquettes
within the fine half-space of time-positive link starts {0,1}.
Free-group words test *all* original bonds without assuming commuting links.
Finite geometry test; not a Wilson RP/OS or continuum YM gap certificate.
"""
from itertools import combinations, product

D = 4

def step(site, axis, n, sign=1):
    result = list(site)
    result[axis] = (result[axis] + sign) % n
    return tuple(result)

def reflect(site, n, shift):
    result = list(site)
    result[0] = (shift - result[0]) % n
    return tuple(result)

def inv(word):
    return tuple((bond, -sgn) for bond, sgn in reversed(word))

def prod(*words):
    reduced = []
    for bond, sgn in (token for word in words for token in word):
        if reduced and reduced[-1] == (bond, -sgn):
            reduced.pop()
        else:
            reduced.append((bond, sgn))
    return tuple(reduced)

def link(site, axis):
    return (((site, axis), 1),)

def reflect_link(site, axis, fine_shift):
    r = reflect(site, 4, fine_shift)
    return inv(link(step(r, 0, 4, -1), 0)) if axis == 0 else link(r, axis)

def block(site, axis):
    even = tuple(2 * t for t in site)
    return prod(link(even, axis), link(step(even, axis, 4), axis))

def reflect_block_coarse(site, axis, fine_shift):
    r = reflect(site, 2, fine_shift // 2)
    return inv(block(step(r, 0, 2, -1), axis)) if axis == 0 else block(r, axis)

def block_reflect_fine(site, axis, fine_shift):
    even = tuple(2 * t for t in site)
    return prod(reflect_link(even, axis, fine_shift),
                reflect_link(step(even, axis, 4), axis, fine_shift))

def plaquette(site, i, j, edge):
    return prod(edge(site, i), edge(step(site, i, 4), j),
                inv(edge(step(site, j, 4), i)), inv(edge(site, j)))

def same_real_trace(word1, word2):
    if len(word1) != len(word2):
        return False
    for target in (word2, inv(word2)):
        if any(word1 == target[k:] + target[:k] for k in range(len(target))):
            return True
    return False

def native_coarse_time_starts(site, axis):
    even = tuple(2 * t for t in site)
    return (even[0], step(even, axis, 4)[0]) if axis == 0 else ()

def selected_plaquette_time_starts(site, i, j):
    sides = ((site, i), (step(site, i, 2), j),
             (step(site, j, 2), i), (site, j))
    return {t for pos, axis in sides
            for t in native_coarse_time_starts(pos, axis)}

def main():
    fine = list(product(range(4), repeat=D))
    coarse = list(product(range(2), repeat=D))
    assert len(fine) == 256 and len(coarse) == 16
    assert 4 * len(fine) == 1024 and 4 * len(coarse) == 64
    for shift in (0, 2):
        assert all(reflect(reflect(x, 4, shift), 4, shift) == x for x in fine)
        assert all(reflect(reflect(x, 2, shift // 2), 2, shift // 2) == x
                   for x in coarse)
        for x, axis in product(coarse, range(D)):
            assert block_reflect_fine(x, axis, shift) == reflect_block_coarse(x, axis, shift)
        count = 0
        for x in fine:
            for i, j in combinations(range(D), 2):
                result = plaquette(x, i, j, lambda pos, axis: reflect_link(pos, axis, shift))
                r = reflect(x, 4, shift)
                if i == 0 or j == 0:
                    r = step(r, 0, 4, -1)
                assert same_real_trace(result, plaquette(r, i, j, link))
                count += 1
        assert count == 1536
    chosen_time_bonds = [(x, 0) for x in coarse if x[0] == 0]
    assert len(chosen_time_bonds) == 8
    assert all(set(native_coarse_time_starts(x, axis)) == {0, 1}
               for x, axis in chosen_time_bonds)
    assert all(set(native_coarse_time_starts((1,) + x[1:], axis)) == {2, 3}
               for x, axis in chosen_time_bonds)
    positive_time_plaquettes = [(x, 0, j) for x in coarse if x[0] == 0
                                for j in (1, 2, 3)]
    assert len(positive_time_plaquettes) == 24
    assert all(selected_plaquette_time_starts(x, i, j) == {0, 1}
               for x, i, j in positive_time_plaquettes)
    # The old shift-2 mirror fixes t=1,3 and splits both two-link paths.
    assert all(not set(native_coarse_time_starts(x, 0)).issubset({1, 2})
               for x in coarse)
    print('PASS both source reflection planes: 64/64 ordered R445 links each')
    print('PASS both planes: 1536/1536 original reflected plaquette real traces each')
    print('PASS 8/8 positive coarse time bonds, 24/24 temporal plaquettes in fine positive half')
    print('PASS source geometry identifies old shift-2 half-space mismatch')
    print('OPEN Agda whole native block/reflection, positive-time word/RP, E1/D1/D2')

if __name__ == '__main__':
    main()
