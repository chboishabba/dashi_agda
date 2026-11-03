#!/usr/bin/env python3
"""Executable reference producer for YM R443.F07's original C3 swap word.

The EXACT original side-four positive-bond order is the nested Cartesian
Torus.periodicTorus4Finite enumeration followed by Axis4. C3 is the
existing CMP119/Weld spatial C3 map, not a newly selected permutation.

Compute the MINIMUM adjacent-transposition word for the resulting finite
permutation by stable left insertion (inversion count). The list records
indices in APPLY ORDER; in Agda's Product.LinkPermutation semantics,
compose first second means 'apply second, then first'. An Agda witness
must still construct that program and kernel-prove the one-vector equation
from YMClayNativeC3SingleVectorPermutationCertificateExact.

This Python script does not typecheck any Agda, build physical SU(N) Haar,
make a physical RG limit or prove a Clay mass gap.
"""

from hashlib import sha256
from itertools import product
import json


def native_labels(side: int):
    assert side >= 1
    return [
        (*site, axis)
        for site in product(range(side), repeat=4)
        for axis in range(4)
    ]


def spatial_c3(bond):
    x0, x1, x2, x3, axis = bond
    return x0, x3, x1, x2, (0, 2, 3, 1)[axis]


def native_c3_permutation(labels):
    position = {label: i for i, label in enumerate(labels)}
    assert len(position) == len(labels)
    return [position[spatial_c3(label)] for label in labels]


def minimal_adjacent_swap_word(perm):
    n = len(perm)
    assert sorted(perm) == list(range(n))
    state = list(range(n))
    where = list(range(n))
    word = []
    for destination, wanted in enumerate(perm):
        j = where[wanted]
        while j > destination:
            left, right = state[j - 1], state[j]
            state[j - 1], state[j] = right, left
            where[left], where[right] = j, j - 1
            word.append(j - 1)
            j -= 1
    assert state == perm
    return word


def apply_adjacent_word(n, word):
    # In the exact order of repeated Product.compose (swapAt i) prior.
    result = list(range(n))
    for i in word:
        assert 0 <= i < n - 1
        result[i], result[i + 1] = result[i + 1], result[i]
    return result


def inversion_count(perm):
    # Independent O(n log n) Fenwick check of minimal swap count.
    n = len(perm)
    tree = [0] * (n + 1)
    def add(i):
        i += 1
        while i <= n:
            tree[i] += 1
            i += i & -i
    def prefix(i):
        i += 1
        out = 0
        while i > 0:
            out += tree[i]
            i -= i & -i
        return out
    inv = 0
    for k, x in enumerate(perm):
        inv += k - prefix(x)
        add(x)
    return inv


def verify(side: int):
    labels = native_labels(side)
    perm = native_c3_permutation(labels)
    word = minimal_adjacent_swap_word(perm)
    assert apply_adjacent_word(len(perm), word) == perm
    assert len(word) == inversion_count(perm)
    assert all(perm[perm[perm[i]]] == i for i in range(len(perm)))
    fixed = sum(perm[i] == i for i in range(len(perm)))
    cycles = (len(perm) - fixed) // 3
    assert fixed == side * side
    assert fixed + 3 * cycles == len(labels)
    digest = sha256(",".join(map(str, word)).encode("ascii")).hexdigest()
    return {
        "side": side, "sites": side ** 4, "positive_bonds": len(labels),
        "c3_fixed_bonds": fixed, "c3_three_cycles": cycles,
        "minimal_adjacent_swaps": len(word), "word_sha256": digest,
        "status": "PASS_REFERENCE_ONLY_NOT_AGDA",
    }


if __name__ == "__main__":
    for L in (1, 2, 3, 4):
        print(json.dumps(verify(L), sort_keys=True))
