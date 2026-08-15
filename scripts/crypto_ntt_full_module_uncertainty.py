#!/usr/bin/env python3
"""Blue-team discovery probe: full-module ML-KEM uncertainty lift.

This script studies a theorem-level structural question rather than an attack:
whether the sharp 128-point finite-field Fourier support uncertainty principle
survives multiplication by the full k x k public ML-KEM matrix, residue by
residue, once each local matrix is invertible over the quadratic field
K_i = F_q[u]/(u^2-gamma_i).

Primary source:
  National Institute of Standards and Technology,
  "Module-Lattice-Based Key-Encapsulation Mechanism Standard", FIPS 203,
  2024. DOI: 10.6028/NIST.FIPS.203.

Uncertainty reference:
  Martino Borello, Patrick Sole,
  "The uncertainty principle over finite fields", Discrete Mathematics 345
  (2022). DOI: 10.1016/j.disc.2021.112670.

The experiment checks the exact structural lift

  supp_source(delta) * supp_residue(A delta) >= 128

under the conditional hypothesis that every one of the 128 local k x k public
matrices is invertible.  In that case local multiplication preserves whether a
quadratic-residue module vector is zero, so residue support is preserved
exactly.  The scalar uncertainty theorem then lifts componentwise to module-
valued signals.

Important distinction:
  * 128 is the sharp actual-value residue-support obstruction.
  * 256*k from existing DASHI butterfly files is a structural scalar dependency
    slot/fanout quantity, not the same notion of support.

No cryptographic break or operational attack is claimed here.
"""

import math
import random
from typing import List, Sequence, Tuple

import numpy as np

Q = 3329
ZETA = 17
HALF = 128
FIELD_SIZE = Q * Q
KZERO = (0, 0)
KONE = (1, 0)


def bitrev7(i: int) -> int:
    return int(f"{i:07b}"[::-1], 2)


def gamma(i: int) -> int:
    return pow(ZETA, 2 * bitrev7(i) + 1, Q)


GAMMAS = tuple(gamma(i) for i in range(HALF))


def kadd(x: Tuple[int, int], y: Tuple[int, int]) -> Tuple[int, int]:
    return ((x[0] + y[0]) % Q, (x[1] + y[1]) % Q)


def ksub(x: Tuple[int, int], y: Tuple[int, int]) -> Tuple[int, int]:
    return ((x[0] - y[0]) % Q, (x[1] - y[1]) % Q)


def kmul(x: Tuple[int, int], y: Tuple[int, int], g: int) -> Tuple[int, int]:
    a0, a1 = x
    b0, b1 = y
    return ((a0 * b0 + g * a1 * b1) % Q, (a0 * b1 + a1 * b0) % Q)


def kinv(x: Tuple[int, int], g: int) -> Tuple[int, int]:
    a, b = x
    denominator = (a * a - g * b * b) % Q
    if denominator == 0:
        raise ZeroDivisionError("non-invertible quadratic-field element")
    inv_denominator = pow(denominator, Q - 2, Q)
    return ((a * inv_denominator) % Q, (-b * inv_denominator) % Q)


def krank(matrix: Sequence[Sequence[Tuple[int, int]]], g: int) -> int:
    a = [[tuple(value) for value in row] for row in matrix]
    rows = len(a)
    cols = len(a[0])
    rank = 0
    for col in range(cols):
        pivot = None
        for row in range(rank, rows):
            if a[row][col] != KZERO:
                pivot = row
                break
        if pivot is None:
            continue
        a[rank], a[pivot] = a[pivot], a[rank]
        pivot_inverse = kinv(a[rank][col], g)
        a[rank] = [kmul(value, pivot_inverse, g) for value in a[rank]]
        for row in range(rows):
            if row == rank:
                continue
            factor = a[row][col]
            if factor != KZERO:
                a[row] = [
                    ksub(a[row][c], kmul(factor, a[rank][c], g))
                    for c in range(cols)
                ]
        rank += 1
        if rank == rows:
            break
    return rank


def matvec(
    matrix: Sequence[Sequence[Tuple[int, int]]],
    vector: Sequence[Tuple[int, int]],
    g: int,
) -> List[Tuple[int, int]]:
    out = []
    for row in matrix:
        acc = KZERO
        for a, b in zip(row, vector):
            acc = kadd(acc, kmul(a, b, g))
        out.append(acc)
    return out


def fips_parity_transform() -> np.ndarray:
    omega = pow(ZETA, 2, Q)
    fourier = np.array(
        [[pow(omega, r * j, Q) for j in range(HALF)] for r in range(HALF)],
        dtype=np.int64,
    )
    diagonal = np.array([pow(ZETA, j, Q) for j in range(HALF)], dtype=np.int64)
    natural = (fourier * diagonal[np.newaxis, :]) % Q
    permutation = np.array([bitrev7(i) for i in range(HALF)], dtype=np.int64)
    return natural[permutation, :]


TFIPS = fips_parity_transform()


def source_vector_position_support(even: np.ndarray, odd: np.ndarray) -> int:
    even_support = sum(np.any(even[:, j] % Q != 0) for j in range(HALF))
    odd_support = sum(np.any(odd[:, j] % Q != 0) for j in range(HALF))
    return int(even_support + odd_support)


def transform_module(even: np.ndarray, odd: np.ndarray):
    constant = (even @ TFIPS.T) % Q
    linear = (odd @ TFIPS.T) % Q
    k = even.shape[0]
    return [
        [(int(constant[j, i]), int(linear[j, i])) for j in range(k)]
        for i in range(HALF)
    ]


def residue_support(vhat) -> int:
    return sum(any(component != KZERO for component in vector) for vector in vhat)


def output_residue_support(public_blocks, vhat) -> int:
    total = 0
    for i, (matrix, vector) in enumerate(zip(public_blocks, vhat)):
        output = matvec(matrix, vector, GAMMAS[i])
        if any(component != KZERO for component in output):
            total += 1
    return total


def output_rowpair_support(public_blocks, vhat) -> int:
    total = 0
    for i, (matrix, vector) in enumerate(zip(public_blocks, vhat)):
        output = matvec(matrix, vector, GAMMAS[i])
        total += sum(component != KZERO for component in output)
    return total


def random_kelt(rng: random.Random) -> Tuple[int, int]:
    return (rng.randrange(Q), rng.randrange(Q))


def random_invertible_matrix(rng: random.Random, k: int, g: int):
    while True:
        matrix = [[random_kelt(rng) for _ in range(k)] for __ in range(k)]
        if krank(matrix, g) == k:
            return matrix


def random_module_public_matrix(rng: random.Random, k: int):
    blocks = []
    ranks = []
    for g in GAMMAS:
        matrix = random_invertible_matrix(rng, k, g)
        blocks.append(matrix)
        ranks.append(krank(matrix, g))
    return blocks, ranks


def ideal_uniform_invertibility_probability(k: int) -> Tuple[float, float]:
    one = 1.0
    for j in range(k):
        one *= 1 - FIELD_SIZE ** (j - k)
    return one, one ** HALF


def run_regression(seed: int = 20260815) -> None:
    rng = random.Random(seed)

    for k in (2, 3, 4):
        public_blocks, ranks = random_module_public_matrix(rng, k)
        assert all(rank == k for rank in ranks)

        violations = 0
        minimum_residue_product = 10**18
        minimum_rowpair_product = 10**18
        equality_hits = 0

        for _ in range(180):
            even = np.zeros((k, HALF), dtype=np.int64)
            odd = np.zeros((k, HALF), dtype=np.int64)

            for parity in (even, odd):
                for __ in range(rng.randrange(0, 5)):
                    position = rng.randrange(HALF)
                    component = rng.randrange(k)
                    parity[component, position] = rng.randrange(1, Q)

            if not np.any(even) and not np.any(odd):
                even[0, rng.randrange(HALF)] = rng.randrange(1, Q)

            transformed = transform_module(even, odd)
            source_support = source_vector_position_support(even, odd)
            transform_support = residue_support(transformed)
            public_support = output_residue_support(public_blocks, transformed)
            rowpair_support = output_rowpair_support(public_blocks, transformed)

            # Full-rank local public matrices preserve zero/nonzero residue
            # vectors exactly.
            if public_support != transform_support:
                violations += 1

            # Vector-valued uncertainty follows by selecting any nonzero module
            # component/parity scalar signal and applying the scalar theorem.
            residue_product = source_support * public_support
            if residue_product < HALF:
                violations += 1

            minimum_residue_product = min(minimum_residue_product, residue_product)
            minimum_rowpair_product = min(minimum_rowpair_product, source_support * rowpair_support)
            if residue_product == HALF:
                equality_hits += 1

        one_probability, all_probability = ideal_uniform_invertibility_probability(k)
        print(f"k={k}")
        print("  all local ranks full:", all(rank == k for rank in ranks))
        print("  violations:", violations)
        print("  min source-support * output-residue-support:", minimum_residue_product)
        print("  sharp residue-support bound:", HALF)
        print("  equality hits:", equality_hits)
        print("  min source-support * output-rowpair-support:", minimum_rowpair_product)
        print("  ideal P(one local matrix invertible):", one_probability)
        print("  ideal P(all 128 local matrices invertible):", all_probability)
        print("  ideal P(any singular):", 1 - all_probability)
        print()

        assert violations == 0
        assert minimum_residue_product >= HALF


if __name__ == "__main__":
    run_regression()
