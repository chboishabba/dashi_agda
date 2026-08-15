#!/usr/bin/env python3
"""Blue-team ML-KEM: lift the 128-point parity uncertainty theorem through BaseCase.

This is exploratory mathematics, not an ML-KEM attack claim.

Primary source:
  NIST FIPS 203, Module-Lattice-Based Key-Encapsulation Mechanism Standard,
  2024. DOI: 10.6028/NIST.FIPS.203.

Uncertainty source:
  Martino Borello, Patrick Sole,
  "The uncertainty principle over finite fields", Discrete Mathematics 345
  (2022), 112670. DOI: 10.1016/j.disc.2021.112670.

The exact analytic point checked here is:

  * each FIPS gamma_i is a nonsquare in F_3329, hence x^2-gamma_i is
    irreducible and BaseCase multiplication by any nonzero local pair is an
    invertible 2x2 F_3329-linear map;
  * therefore a nonzero quadratic NTT residue of a secret perturbation cannot
    disappear in a public row unless the corresponding public A residue itself
    is zero;
  * if d_i is the number of nonzero public-row multipliers at residue i and
    d_min=min_i d_i, then

        coeffSupport(delta) * verifierPairSupport(A*delta) >= 128*d_min.

When all k public-row multipliers are nonzero at every residue, this gives the
actual-value pair-support lower bound 128*k.  Separately, each active BaseCase
pair structurally touches two scalar outputs, giving the already-observed
structural fanout product 256*k.  These are deliberately kept distinct: 256*k
is a dependency-slot invariant, not a deterministic scalar nonzero-support
bound.
"""

from __future__ import annotations

import math
import random

import numpy as np

Q = 3329
ZETA = 17
HALF = 128


def bitrev7(i: int) -> int:
    return int(f"{i:07b}"[::-1], 2)


def gamma(i: int) -> int:
    return pow(ZETA, 2 * bitrev7(i) + 1, Q)


def legendre(a: int) -> int:
    return pow(a % Q, (Q - 1) // 2, Q)


def basecase(a: tuple[int, int], s: tuple[int, int], g: int) -> tuple[int, int]:
    a0, a1 = a
    s0, s1 = s
    return (
        (a0 * s0 + g * a1 * s1) % Q,
        (a1 * s0 + a0 * s1) % Q,
    )


def determinant(a: tuple[int, int], g: int) -> int:
    a0, a1 = a
    return (a0 * a0 - g * a1 * a1) % Q


def cyclic_fourier_parity_matrix() -> np.ndarray:
    omega = pow(ZETA, 2, Q)
    fourier = np.array(
        [[pow(omega, r * j, Q) for j in range(HALF)] for r in range(HALF)],
        dtype=np.int64,
    )
    diagonal = np.array([pow(ZETA, j, Q) for j in range(HALF)], dtype=np.int64)
    return (fourier * diagonal[np.newaxis, :]) % Q


def support(v: np.ndarray) -> int:
    return int(np.count_nonzero(np.asarray(v) % Q))


def verify_irreducible_basecase_factors() -> None:
    gammas = [gamma(i) for i in range(HALF)]
    assert all(legendre(g) == Q - 1 for g in gammas)

    # If a1 != 0, gamma*a1^2 is nonsquare, while a0^2 is square.  Therefore
    # a0^2 = gamma*a1^2 is impossible.  If a1=0, determinant zero forces a0=0.
    for g in gammas:
        assert determinant((0, 0), g) == 0
        for a1 in (1, 2, 17, 1729, Q - 1):
            assert legendre((g * a1 * a1) % Q) == Q - 1


def active_degree(public_rows: list[list[tuple[int, int]]]) -> int:
    # public_rows[r][i] is the local quadratic A multiplier at row r,residue i.
    per_residue = []
    for i in range(HALF):
        per_residue.append(sum(public_rows[r][i] != (0, 0) for r in range(len(public_rows))))
    return min(per_residue)


def verifier_pair_support(
    public_rows: list[list[tuple[int, int]]], transformed_delta: np.ndarray
) -> int:
    total = 0
    for i, value in enumerate(transformed_delta.tolist()):
        if value % Q == 0:
            continue
        secret_pair = (int(value), 0)
        g = gamma(i)
        for row in public_rows:
            if basecase(row[i], secret_pair, g) != (0, 0):
                total += 1
    return total


def random_nonzero_pair(rng: random.Random) -> tuple[int, int]:
    while True:
        pair = (rng.randrange(Q), rng.randrange(Q))
        if pair != (0, 0):
            return pair


def verify_lift_randomly() -> None:
    rng = random.Random(20260815)
    transform = cyclic_fourier_parity_matrix()

    for k in (2, 3, 4):
        for _ in range(80):
            public_rows = [
                [random_nonzero_pair(rng) for _ in range(HALF)] for _ in range(k)
            ]
            d_min = active_degree(public_rows)
            assert d_min == k

            coeff_support = rng.choice((1, 2, 4, 8, 16, 32))
            delta = np.zeros(HALF, dtype=np.int64)
            for j in rng.sample(range(HALF), coeff_support):
                delta[j] = rng.randrange(1, Q)

            transformed = (transform @ delta) % Q
            residue_support = support(transformed)
            verifier_support = verifier_pair_support(public_rows, transformed)

            # Borello-Sole naive finite-field UP, specialized to n=128:
            assert coeff_support * residue_support >= HALF
            # BaseCase local invertibility multiplies residue support by d_min.
            assert verifier_support == d_min * residue_support
            assert coeff_support * verifier_support >= HALF * d_min


def print_parameter_bounds() -> None:
    zero_probability = 1 / (Q * Q)
    print("local A residue zero probability:", zero_probability)
    for k in (2, 3, 4):
        blocks = HALF * k
        p_all_nonzero = (1 - zero_probability) ** blocks
        print(
            f"k={k}: P(all {blocks} local multipliers nonzero)={p_all_nonzero:.12f}; "
            f"actual pair-support lower bound={HALF*k}; "
            f"structural scalar-slot product={2*HALF*k}"
        )


def main() -> None:
    verify_irreducible_basecase_factors()
    print("PASS: all 128 gamma_i are nonsquares; nonzero BaseCase multipliers invertible")
    verify_lift_randomly()
    print("PASS: random exact-value checks satisfy coeffSupport*verifierPairSupport >= 128*d_min")
    print_parameter_bounds()


if __name__ == "__main__":
    main()
