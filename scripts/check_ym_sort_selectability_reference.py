#!/usr/bin/env python3
"""Fail-closed exact finite reference for original Agda AllSelectable.

Not an Agda kernel, Haar measure, continuum or Clay proof.
"""
from itertools import product, permutations
from hashlib import sha256
import json

def canonical(side):
    return [(site, axis) for site in product(range(side), repeat=4)
            for axis in range(4)]

def c3(bond):
    (t, x, y, z), a = bond
    return ((t, z, x, y), (0, 2, 3, 1)[a])

def pair_target():
    coarse = [(site, axis) for site in product(range(2), repeat=4)
              for axis in range(4)]
    selected = []
    for site, axis in coarse:
        origin = tuple(2*x for x in site)
        second = list(origin)
        second[axis] = (second[axis]+1) % 4
        selected.extend(((origin, axis), (tuple(second), axis)))
    original = canonical(4)
    distinct = set(selected)
    assert len(distinct) == 128
    spectator = [x for x in original if x not in distinct]
    assert len(spectator) == 896
    return selected + spectator

def sort_with_trace(source, target):
    assert len(source) == len(target)
    current = list(source)
    word = []
    steps = 0
    for i, wanted in enumerate(target):
        assert wanted in current[i:], ('missing-member', i, wanted)
        at = current.index(wanted, i)
        while at > i:
            current[at-1], current[at] = current[at], current[at-1]
            word.append(at-1)
            at -= 1
        assert current[i] == wanted
        steps += 1
    assert current == list(target)
    return steps, word

def main():
    checked = 0
    for n in range(8):
        canonical_source = list(range(n))
        for target in permutations(canonical_source):
            steps, word = sort_with_trace(canonical_source, target)
            assert steps == n
            checked += 1
    labels = canonical(4)
    c3target = [c3(x) for x in labels]
    steps1, w1 = sort_with_trace(labels, c3target)
    steps2, w2 = sort_with_trace(labels, pair_target())
    assert steps1 == steps2 == 1024
    assert len(w1) == 46592 and len(w2) == 41792
    assert sha256(','.join(map(str,w1)).encode()).hexdigest() == 'a61adb9c6fe7bbfaa12f9255f8fd0fc139e26991e5c158e0643cfa174eca4dc7'
    assert all(c3(c3(c3(x))) == x for x in labels)
    for original, target in (([0,1,2],[0,1,1]),([0,1,2],[0,1,3])):
        try:
            sort_with_trace(original,target)
        except AssertionError:
            pass
        else:
            raise AssertionError('invalid target falsely accepted')
    print(json.dumps({'exhaustive_distinct_small_permutations':checked,
                      'original_bonds':len(labels), 'actual_c3_sort_steps':steps1,
                      'actual_pair_spectator_sort_steps':steps2,
                      'c3_swaps':len(w1),'block_swaps':len(w2),
                      'negative_controls':'PASS',
                      'scope':'PYTHON_REFERENCE_NOT_AGDA_OR_PHYSICAL'},indent=2))

if __name__=='__main__': main()
