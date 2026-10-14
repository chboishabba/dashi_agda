#!/usr/bin/env python3
from __future__ import annotations

import itertools
from collections import defaultdict
import numpy as np

P = 101


def permutation_sign(perm):
    inversions = sum(
        1 for i in range(len(perm)) for j in range(i + 1, len(perm))
        if perm[i] > perm[j]
    )
    return -1 if inversions % 2 else 1


def cubic_terms():
    terms = defaultdict(int)
    for base in (0, 9, 18):
        for perm in itertools.permutations(range(3)):
            mon = tuple(sorted(base + 3 * i + perm[i] for i in range(3)))
            terms[mon] += permutation_sign(perm)
    for i in range(3):
        for j in range(3):
            for k in range(3):
                mon = tuple(sorted((3 * i + j, 9 + 3 * j + k, 18 + 3 * k + i)))
                terms[mon] -= 1
    return {mon: coeff for mon, coeff in terms.items() if coeff}


def cubic_invariance_matrix():
    monomials = list(itertools.combinations_with_replacement(range(27), 3))
    mon_index = {mon: i for i, mon in enumerate(monomials)}
    matrix = np.zeros((len(monomials), 729), dtype=np.int16)
    for mon, coeff in cubic_terms().items():
        factors = list(mon)
        for pos, output_coordinate in enumerate(factors):
            others = factors[:pos] + factors[pos + 1:]
            for input_coordinate in range(27):
                target = tuple(sorted(others + [input_coordinate]))
                matrix[mon_index[target], output_coordinate * 27 + input_coordinate] += coeff
    return matrix[np.any(matrix != 0, axis=1)]


def rank_mod_p(matrix, p=P):
    a = np.asarray(matrix, dtype=np.int64).copy() % p
    m, n = a.shape
    rank = 0
    for col in range(n):
        pivots = np.flatnonzero(a[rank:, col])
        if pivots.size == 0:
            continue
        pivot = rank + int(pivots[0])
        if pivot != rank:
            a[[rank, pivot]] = a[[pivot, rank]]
        a[rank] = a[rank] * pow(int(a[rank, col]), -1, p) % p
        rows = np.flatnonzero(a[rank + 1:, col]) + rank + 1
        if rows.size:
            factors = a[rows, col].copy()
            a[rows] = (a[rows] - factors[:, None] * a[rank]) % p
        rank += 1
        if rank == m:
            break
    return rank


def sl3_basis():
    out = []
    for i in range(3):
        for j in range(3):
            if i != j:
                m = np.zeros((3, 3), dtype=int)
                m[i, j] = 1
                out.append(m)
    out.append(np.diag([1, -1, 0]))
    out.append(np.diag([0, 1, -1]))
    assert len(out) == 8
    return out


def unpack(v):
    return [v[0:9].reshape(3,3), v[9:18].reshape(3,3), v[18:27].reshape(3,3)]


def flatten(blocks):
    return np.concatenate([b.reshape(-1) for b in blocks])


def infinitesimal_trinification(factor, h):
    d = np.zeros((27, 27), dtype=int)
    for j in range(27):
        e = np.zeros(27, dtype=int); e[j] = 1
        x, y, z = unpack(e)
        if factor == 0:
            image = (h @ x, np.zeros((3,3), int), -z @ h)
        elif factor == 1:
            image = (-x @ h, h @ y, np.zeros((3,3), int))
        else:
            image = (np.zeros((3,3), int), -y @ h, h @ z)
        d[:, j] = flatten(image)
    return d


def zero_coordinate_constraints(predicate):
    rows = []
    for output in range(27):
        for input_coordinate in range(27):
            if predicate(output, input_coordinate):
                row = np.zeros(729, dtype=np.int16)
                row[output * 27 + input_coordinate] = 1
                rows.append(row)
    return np.asarray(rows, dtype=np.int16)


def fixed_vector_constraints(indices):
    rows = []
    for input_coordinate in indices:
        for output in range(27):
            row = np.zeros(729, dtype=np.int16)
            row[output * 27 + input_coordinate] = 1
            rows.append(row)
    return np.asarray(rows, dtype=np.int16)


def verify():
    cubic = cubic_invariance_matrix()
    e6_dim = 729 - rank_mod_p(cubic)
    assert e6_dim == 78

    # Commuting with sigma_zeta=diag(1,zeta,zeta^2) is exactly block preservation
    # once zeta has three distinct eigenvalues.
    off_block = zero_coordinate_constraints(lambda o, i: (o // 9) != (i // 9))
    centralizer_dim = 729 - rank_mod_p(np.vstack([cubic, off_block]))
    assert centralizer_dim == 24

    tri = [infinitesimal_trinification(factor, h) for factor in range(3) for h in sl3_basis()]
    tri_flat = np.asarray([d.reshape(-1) for d in tri], dtype=int)
    tri_dim = rank_mod_p(tri_flat.T)
    assert tri_dim == 24
    tri_preserves = all(np.all((cubic @ d.reshape(-1)) == 0) for d in tri)
    tri_block = all(
        all(d[o, i] == 0 for o in range(27) for i in range(27) if o // 9 != i // 9)
        for d in tri
    )
    assert tri_preserves and tri_block

    # Directly fixing the two neutral vectors E32,E33 in the first block leaves
    # a much larger full-E6 infinitesimal stabilizer than the SM gauge algebra.
    pair_constraints = fixed_vector_constraints([7, 8])
    pair_stabilizer_dim = 729 - rank_mod_p(np.vstack([cubic, pair_constraints]))
    assert pair_stabilizer_dim == 49

    # Repeat the two dimension checks at several good primes as a rank-stability audit.
    stable = True
    for p in (101, 103, 107, 109, 127):
        stable &= (729 - rank_mod_p(cubic, p) == 78)
        stable &= (729 - rank_mod_p(np.vstack([cubic, off_block]), p) == 24)
        stable &= (729 - rank_mod_p(np.vstack([cubic, pair_constraints]), p) == 49)
    assert stable

    return {
        "e6_norm_symmetry_dimension": e6_dim,
        "zeta_centralizer_dimension": centralizer_dim,
        "explicit_trinification_dimension": tri_dim,
        "explicit_trinification_preserves_cubic": tri_preserves,
        "explicit_trinification_commutes_with_zeta_grading": tri_block,
        "centralizer_equals_trinification_by_inclusion_and_dimension": True,
        "two_vev_full_e6_stabilizer_dimension": pair_stabilizer_dim,
        "rank_stable_at_primes": [101, 103, 107, 109, 127],
        "two_vev_direct_e6_to_sm_claim": False,
        "physical_zeta_order_parameter_paid": False,
    }


if __name__ == "__main__":
    for key, value in verify().items():
        print(f"{key}: {value}")
