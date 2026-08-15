#!/usr/bin/env python3
"""ML-KEM full-module uncertainty with a singular-residue budget.

Blue-team / theorem-discovery probe.  This does not claim an attack.

Primary source:
  National Institute of Standards and Technology,
  "Module-Lattice-Based Key-Encapsulation Mechanism Standard", FIPS 203,
  2024. DOI: 10.6028/NIST.FIPS.203.

Finite-field uncertainty source:
  Martino Borello, Patrick Sole,
  "The uncertainty principle over finite fields", Discrete Mathematics 345
  (2022), 112670. DOI: 10.1016/j.disc.2021.112670.

For a nonzero module perturbation delta define

  s = coefficient-position support of delta,
  h = quadratic-residue support of NTT(delta),
  o = quadratic-residue support of Ahat * NTT(delta),
  sigma = number of singular local public matrices Ahat_i.

Local linear algebra gives

  h <= o + sigma,

because a nonzero active residue can disappear only at a singular local matrix.
The 128-point finite-field Fourier uncertainty theorem gives

  128 <= s * h.

Hence the robust public-matrix inequality

  128 <= s * (o + sigma).

When sigma=0 this reduces to the exact full-rank lift

  128 <= s * o.

The script regresses the local and combined inequalities for k=2,3,4, across
both parity blocks and multiple module coordinates.  It also deliberately uses
rank-(k-1) singular blocks whose kernel is known, so the singular-budget term is
actually exercised rather than merely present vacuously.
"""

import random

import numpy as np

Q = 3329
ZETA = 17
HALF = 128
KZERO = (0, 0)
KONE = (1, 0)


def bitrev7(i: int) -> int:
    return int(f"{i:07b}"[::-1], 2)


def gamma(i: int) -> int:
    return pow(ZETA, 2 * bitrev7(i) + 1, Q)


GAMMAS = tuple(gamma(i) for i in range(HALF))


def kadd(x, y):
    return ((x[0] + y[0]) % Q, (x[1] + y[1]) % Q)


def ksub(x, y):
    return ((x[0] - y[0]) % Q, (x[1] - y[1]) % Q)


def kmul(x, y, g):
    return (
        (x[0] * y[0] + g * x[1] * y[1]) % Q,
        (x[0] * y[1] + x[1] * y[0]) % Q,
    )


def kinv(x, g):
    a, b = x
    den = (a * a - g * b * b) % Q
    if den == 0:
        raise ZeroDivisionError("zero quadratic-field denominator")
    d = pow(den, Q - 2, Q)
    return ((a * d) % Q, (-b * d) % Q)


def krank(matrix, g):
    a = [[tuple(value) for value in row] for row in matrix]
    rows = len(a)
    cols = len(a[0])
    r = 0
    for c in range(cols):
        pivot = next((rr for rr in range(r, rows) if a[rr][c] != KZERO), None)
        if pivot is None:
            continue
        a[r], a[pivot] = a[pivot], a[r]
        inverse = kinv(a[r][c], g)
        a[r] = [kmul(value, inverse, g) for value in a[r]]
        for rr in range(rows):
            if rr == r:
                continue
            factor = a[rr][c]
            if factor != KZERO:
                a[rr] = [
                    ksub(a[rr][cc], kmul(factor, a[r][cc], g))
                    for cc in range(cols)
                ]
        r += 1
        if r == rows:
            break
    return r


def matvec(matrix, vector, g):
    result = []
    for row in matrix:
        acc = KZERO
        for a, b in zip(row, vector):
            acc = kadd(acc, kmul(a, b, g))
        result.append(acc)
    return result


def random_kelt(rng):
    return (rng.randrange(Q), rng.randrange(Q))


def random_full_rank_matrix(rng, k, g):
    while True:
        matrix = [[random_kelt(rng) for _ in range(k)] for __ in range(k)]
        if krank(matrix, g) == k:
            return matrix


def singular_diag_matrix(k):
    """Rank k-1 with kernel spanned by the first basis vector."""
    matrix = [[KZERO for _ in range(k)] for __ in range(k)]
    for j in range(1, k):
        matrix[j][j] = KONE
    return matrix


def fips_parity_matrix():
    omega = pow(ZETA, 2, Q)
    fourier = np.array(
        [[pow(omega, r * j, Q) for j in range(HALF)] for r in range(HALF)],
        dtype=np.int64,
    )
    diagonal = np.array([pow(ZETA, j, Q) for j in range(HALF)], dtype=np.int64)
    natural = (fourier * diagonal[np.newaxis, :]) % Q
    permutation = np.array([bitrev7(i) for i in range(HALF)], dtype=np.int64)
    return natural[permutation, :]


TFIPS = fips_parity_matrix()


def transform_module(even, odd):
    constant = (even @ TFIPS.T) % Q
    linear = (odd @ TFIPS.T) % Q
    k = even.shape[0]
    return [
        [(int(constant[j, i]), int(linear[j, i])) for j in range(k)]
        for i in range(HALF)
    ]


def source_support(even, odd):
    return int(
        sum(np.any(even[:, j] % Q != 0) for j in range(HALF))
        + sum(np.any(odd[:, j] % Q != 0) for j in range(HALF))
    )


def residue_support(vhat):
    return sum(any(value != KZERO for value in block) for block in vhat)


def output_support(public_blocks, vhat):
    return sum(
        any(value != KZERO for value in matvec(public_blocks[i], vhat[i], GAMMAS[i]))
        for i in range(HALF)
    )


def run_regression(seed=20260815):
    rng = random.Random(seed)
    rows = []
    for k in (2, 3, 4):
        for singular_count in (0, 1, 2, 4, 8, 16, 32):
            local_violations = 0
            budget_violations = 0
            min_budget_product = 10**9
            max_killed = 0

            for _ in range(80):
                singular_set = set(rng.sample(range(HALF), singular_count))
                public_blocks = [
                    singular_diag_matrix(k)
                    if i in singular_set
                    else random_full_rank_matrix(rng, k, GAMMAS[i])
                    for i in range(HALF)
                ]

                even = np.zeros((k, HALF), dtype=np.int64)
                odd = np.zeros((k, HALF), dtype=np.int64)
                for parity in (even, odd):
                    for __ in range(rng.randrange(0, 6)):
                        parity[rng.randrange(k), rng.randrange(HALF)] = rng.randrange(1, Q)
                if not np.any(even) and not np.any(odd):
                    even[0, rng.randrange(HALF)] = rng.randrange(1, Q)

                vhat = transform_module(even, odd)
                s = source_support(even, odd)
                h = residue_support(vhat)
                o = output_support(public_blocks, vhat)

                if h > o + singular_count:
                    local_violations += 1
                if s * (o + singular_count) < HALF:
                    budget_violations += 1

                min_budget_product = min(min_budget_product, s * (o + singular_count))
                max_killed = max(max_killed, h - o)

            rows.append(
                (
                    k,
                    singular_count,
                    local_violations,
                    budget_violations,
                    min_budget_product,
                    max_killed,
                )
            )
    return rows


def main():
    rows = run_regression()
    print("k sigma localViol budgetViol minProduct maxKilled")
    for row in rows:
        print(*row)
        assert row[2] == 0
        assert row[3] == 0
        assert row[4] >= HALF
        assert row[5] <= row[1]
    print("PASS: h <= o + sigma across all regressions")
    print("PASS: 128 <= s * (o + sigma) across all regressions")


if __name__ == "__main__":
    main()
