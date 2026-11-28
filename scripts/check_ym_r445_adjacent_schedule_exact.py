#!/usr/bin/env python3
"""Exact original 1024-bond list reorder as consecutive transpositions.

Source geometry uses the 4D canonical site/axis enumeration and the
side-two coarse-bond/first-then-second axial-phase ordering. This is an
independent finite test, not a kernel-accepted Agda schedule witness.
"""
from hashlib import sha256
from itertools import product
from random import Random

FINE = tuple((*x, d) for x in product(range(4), repeat=4) for d in range(4))
COARSE = tuple((*x, d) for x in product(range(2), repeat=4) for d in range(4))


def pair_bond(bond, phase):
    x = [2 * value for value in bond[:4]]
    x[bond[4]] += phase
    return (*x, bond[4])


def swap_schedule(target_indices):
    current = list(range(len(target_indices)))
    positions = []
    for dst, wanted in enumerate(target_indices):
        src = current.index(wanted, dst)
        for position in range(src - 1, dst - 1, -1):
            current[position], current[position + 1] = current[position + 1], current[position]
            positions.append(position)
    assert tuple(current) == tuple(target_indices)
    return tuple(positions)


def main():
    selected = tuple(pair_bond(b, p) for b in COARSE for p in (0, 1))
    residual = tuple(b for b in FINE if b not in set(selected))
    assert (len(FINE), len(COARSE), len(selected), len(residual)) == (1024, 64, 128, 896)
    lookup = {bond: idx for idx, bond in enumerate(FINE)}
    target = tuple(lookup[b] for b in selected + residual)
    schedule = swap_schedule(target)
    assert len(schedule) == 41792
    assert all(0 <= p < 1023 for p in schedule)
    assert sha256(','.join(map(str, target)).encode()).hexdigest() == '49b954c21ccd1649208074eb5096e5b6b63102313da773fe17e1268b67727ada'
    assert sha256(','.join(map(str, schedule)).encode()).hexdigest() == '9d75eed2b46c4507c92a699a337413b3bed9d41580c4ac616228f2dad82562cd'
    rng = Random(14441444)
    for _ in range(12):
        values = [rng.randrange(-200, 200) for _ in FINE]
        permuted = values.copy()
        for position in schedule:
            permuted[position], permuted[position+1] = permuted[position+1], permuted[position]
        assert permuted == [values[j] for j in target]
    print('PASS: 41,792 legal adjacent transpositions realize 1024-bond canonical-to-pair/residual reordering')
    print('PASS: 12 exact vector actions, matching fixed canonical permutation and schedule hashes')
    print('No source-level Agda schedule witness or kernel acceptance implied')


if __name__ == '__main__':
    main()
