#!/usr/bin/env python3
"""Exhaustive source-shaped R445 side-four positive-bond index audit.

Source geometry: periodicTorus4Finite/cartesian in CyclicIndex order,
with axis as the innermost source bond dimension. These are the 1024
source index labels, not an alternate numerical gauge-field model.

Proves computationally: 64 coarse bonds x 2 selected phases are 128
distinct original side-four positive bonds; 896 complement bonds;
their concatenated 1024 source rank indices form a permutation.

A Python exhaustive certificate is NOT an Agda kernel proof of the
source bond-codec permutation, let alone the interacting Wilson RG.
"""
from hashlib import sha256
from itertools import product

FINE_SIDE = 4
COARSE_SIDE = 2
AXES = range(4)


def source_bonds(side):
    return tuple((*point, axis)
                 for point in product(range(side), repeat=4)
                 for axis in AXES)


def axial_pair_bond(coarse_bond, phase):
    point = [2 * coordinate for coordinate in coarse_bond[:4]]
    axis = coarse_bond[4]
    point[axis] = (point[axis] + phase) % FINE_SIDE
    return (*point, axis)


def decoder(fine_bond):
    point, axis = fine_bond[:4], fine_bond[4]
    if any(point[k] % 2 for k in AXES if k != axis):
        return None
    coarse = tuple(point[k] // 2 for k in AXES)
    return (*coarse, axis), point[axis] % 2


def main():
    fine = source_bonds(FINE_SIDE)
    coarse = source_bonds(COARSE_SIDE)
    pairs = tuple(axial_pair_bond(C, phase)
                  for C in coarse for phase in range(2))
    rank = {bond: i for i, bond in enumerate(fine)}
    selected = set(pairs)
    residual = tuple(b for b in fine if b not in selected)
    permutation = tuple(rank[b] for b in (*pairs, *residual))
    assert (len(coarse), len(fine), len(pairs), len(selected), len(residual)) == (
        64, 1024, 128, 128, 896)
    assert len(set(permutation)) == 1024
    assert set(permutation) == set(range(1024))
    assert len(set(pairs).intersection(residual)) == 0
    assert all(decoder(axial_pair_bond(C, i)) == (C, i)
               for C in coarse for i in range(2))
    assert all(decoder(b) is None for b in residual)
    assert all(decoder(b) is not None for b in pairs)
    assert all(permutation[i] == rank[pairs[i]] for i in range(128))
    checksum = sha256(",".join(map(str, permutation)).encode()).hexdigest()
    assert checksum == (
        "49b954c21ccd1649208074eb5096e5b6b63102313da773fe17e1268b67727ada")
    print("PASS source-shaped R445: 64 coarse / 128 pair / 896 residual, "
          "1024 distinct and complete rank indices")
    print("permutation sha256:", checksum)


if __name__ == "__main__":
    main()
