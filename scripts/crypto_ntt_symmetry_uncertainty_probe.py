#!/usr/bin/env python3
"""Blue-team ML-KEM symmetry / uncertainty discovery probe.

This is exploratory mathematics, not an ML-KEM attack claim.  It studies the
128-point parity block underlying the FIPS-203 quadratic NTT and records the
symmetry/uncertainty structure that is a candidate for later Agda formalisation.

Primary source:
  National Institute of Standards and Technology,
  "Module-Lattice-Based Key-Encapsulation Mechanism Standard", FIPS 203,
  2024. DOI: 10.6028/NIST.FIPS.203.

Finite-field uncertainty theorem used here:
  Martino Borello, Patrick Sole,
  "The uncertainty principle over finite fields", Discrete Mathematics 345
  (2022). DOI: 10.1016/j.disc.2021.112670.
  Proposition 2 (Naive UP): when gcd(n,q)=1, every nonzero f in F_q^n obeys

      wt_H(f) * wt_H(f-hat) >= n,

  for the Mattson-Solomon / finite-field Fourier transform.  Its proof uses the
  BCH bound: a weight-w polynomial cannot have w consecutive roots among powers
  of a primitive n-th root of unity.

Classical comparison:
  David L. Donoho, Philip B. Stark,
  "Uncertainty Principles and Signal Recovery", SIAM J. Appl. Math. 49 (1989).
  DOI: 10.1137/0149053.

For the FIPS parity block the exact identity checked below is

    T_fips = P_bitrev * F_omega * diag(zeta^j),

where q=3329, zeta=17 has order 256, omega=zeta^2 has order 128, P_bitrev is a
row permutation, and diag(zeta^j) has no zero diagonal entries.  Consequently
both support cardinalities are unchanged by the wrappers around F_omega, so the
Borello-Sole Proposition 2 specializes directly to

    x != 0  ==>  |supp x| * |supp(T_fips x)| >= 128.

The script also constructs sharp equality cases for every divisor d | 128:
character-twisted indicators of a subgroup of size d have transformed support
128/d.  These are the subgroup/character sectors suggested by the SSP symmetry
architecture and are the likely equality objects for the later Agda theorem.
"""

from collections import Counter
import math
import random

import numpy as np

Q = 3329
N = 256
HALF = 128
ZETA = 17
ODD_UNITS = tuple(range(1, 512, 2))


def bitrev7(i: int) -> int:
    return int(f"{i:07b}"[::-1], 2)


def gamma(i: int) -> int:
    return pow(ZETA, 2 * bitrev7(i) + 1, Q)


def multiplicative_order(a: int) -> int:
    x = 1
    for d in range(1, Q):
        x = (x * a) % Q
        if x == 1:
            return d
    raise AssertionError("multiplicative order not found")


def sigma(poly: np.ndarray, a: int) -> np.ndarray:
    out = np.zeros(N, dtype=np.int64)
    for j, c in enumerate(np.asarray(poly, dtype=np.int64) % Q):
        e = (a * j) % (2 * N)
        if e >= N:
            out[e - N] = (out[e - N] - int(c)) % Q
        else:
            out[e] = (out[e] + int(c)) % Q
    return out


def natural_parity_ntt_matrix() -> np.ndarray:
    # Natural residue order alpha_r = zeta^(2r+1).  FIPS uses a bit-reversal
    # permutation of these same 128 points, which does not change support size.
    alpha = [pow(ZETA, 2 * r + 1, Q) for r in range(HALF)]
    return np.array(
        [[pow(alpha[r], j, Q) for j in range(HALF)] for r in range(HALF)],
        dtype=np.int64,
    )


def cyclic_fourier_matrix() -> np.ndarray:
    omega = pow(ZETA, 2, Q)
    return np.array(
        [[pow(omega, r * j, Q) for j in range(HALF)] for r in range(HALF)],
        dtype=np.int64,
    )


def fips_parity_ntt_matrix() -> np.ndarray:
    w = np.empty((HALF, HALF), dtype=np.int64)
    for i in range(HALF):
        g = gamma(i)
        p = 1
        for j in range(HALF):
            w[i, j] = p
            p = (p * g) % Q
    return w


def stabilizer(poly: np.ndarray) -> tuple[int, ...]:
    return tuple(a for a in ODD_UNITS if np.array_equal(sigma(poly, a), poly % Q))


def random_public(rng: random.Random) -> np.ndarray:
    return np.array([rng.randrange(Q) for _ in range(N)], dtype=np.int64)


def random_sparse_vector(rng: random.Random, support_size: int) -> np.ndarray:
    x = np.zeros(HALF, dtype=np.int64)
    for j in rng.sample(range(HALF), support_size):
        value = 0
        while value == 0:
            value = rng.randrange(Q)
        x[j] = value
    return x


def support(x: np.ndarray) -> int:
    return int(np.count_nonzero(np.asarray(x) % Q))


def verify_naive_up_hypotheses() -> None:
    """Check the concrete arithmetic hypotheses of Borello-Sole Proposition 2."""
    assert math.gcd(HALF, Q) == 1
    assert (Q - 1) % HALF == 0
    assert multiplicative_order(ZETA) == 256
    assert multiplicative_order(pow(ZETA, 2, Q)) == HALF


def verify_fourier_equivalence() -> tuple[np.ndarray, np.ndarray]:
    omega = pow(ZETA, 2, Q)
    verify_naive_up_hypotheses()

    natural = natural_parity_ntt_matrix()
    fourier = cyclic_fourier_matrix()
    diagonal = np.array([pow(ZETA, j, Q) for j in range(HALF)], dtype=np.int64)
    assert np.all(diagonal != 0)
    assert np.array_equal(natural, (fourier * diagonal[np.newaxis, :]) % Q)

    # FIPS gamma_i is exactly the bit-reversal permutation of natural rows.
    permutation = [bitrev7(i) for i in range(HALF)]
    assert sorted(permutation) == list(range(HALF))
    assert np.array_equal(fips_parity_ntt_matrix(), natural[permutation, :])
    return natural, fourier


def verify_subgroup_equality_cases(fourier: np.ndarray) -> None:
    # H_d = {0, N/d, ..., (d-1)N/d}.  Character-twisted indicators of H_d
    # have Fourier support N/d, giving exact product N for every d | N.
    omega = pow(ZETA, 2, Q)
    for d in (1, 2, 4, 8, 16, 32, 64, 128):
        stride = HALF // d
        for character in (0, 1, 3):
            x = np.zeros(HALF, dtype=np.int64)
            for t in range(d):
                j = t * stride
                x[j] = pow(omega, character * j, Q)
            y = (fourier @ x) % Q
            assert support(x) == d
            assert support(y) == HALF // d
            assert support(x) * support(y) == HALF

            # Diagonal modulation transports the same sharp product to the
            # natural FIPS parity evaluation map.
            unmodulated = np.array(
                [(int(x[j]) * pow(ZETA, -j, Q)) % Q for j in range(HALF)],
                dtype=np.int64,
            )
            natural_y = (natural_parity_ntt_matrix() @ unmodulated) % Q
            assert support(unmodulated) == d
            assert support(natural_y) == HALF // d
            assert support(unmodulated) * support(natural_y) == HALF


def exact_two_sparse_extremizers() -> list[tuple[int, int, int, int, int]]:
    # For x=e_a+c e_b with d=b-a, zeros satisfy alpha_i^d=-1/c.
    # The largest possible zero set for gap d is therefore exactly the largest
    # fibre of alpha -> alpha^d over the 128 evaluation points.
    alpha = [pow(ZETA, 2 * r + 1, Q) for r in range(HALF)]
    rows = []
    for d in range(1, HALF):
        fibres = Counter(pow(g, d, Q) for g in alpha)
        max_zeros = max(fibres.values())
        min_out = HALF - max_zeros
        rows.append((d, math.gcd(d, HALF), max_zeros, min_out, 2 * min_out))
    return rows


def main() -> None:
    rng = random.Random(20260815)
    verify_naive_up_hypotheses()
    print("PASS: Borello-Sole Naive-UP hypotheses hold for n=128, q=3329")

    natural, fourier = verify_fourier_equivalence()
    print("PASS: FIPS parity block = row-permuted F_omega * diag(zeta^j)")
    print("THEOREM: x != 0 => |supp x| * |supp(T_fips x)| >= 128")
    print("         by Borello-Sole Proposition 2 plus the exact equivalence above")

    verify_subgroup_equality_cases(fourier)
    print("PASS: exact subgroup/character equality cases attain product 128")

    print("generic public stabilizers under X -> X^a")
    sizes = [len(stabilizer(random_public(rng))) for _ in range(12)]
    print("sizes:", sizes)
    print("mean:", sum(sizes) / len(sizes))
    print()

    print("empirical coefficient-support / residue-support tradeoff")
    for k in (1, 2, 3, 4, 8, 16, 32, 64, 128):
        reps = 200 if k <= 16 else 80
        products = []
        outs = []
        for _ in range(reps):
            x = random_sparse_vector(rng, k)
            y = (natural @ x) % Q
            outs.append(support(y))
            products.append(k * support(y))
        print(
            f"k={k:3d} mean_out={sum(outs)/len(outs):8.3f} "
            f"min_out={min(outs):3d} min_product={min(products):5d}"
        )
    print()

    rows = exact_two_sparse_extremizers()
    rows.sort(key=lambda row: (row[4], row[0]))
    print("exact two-sparse extrema")
    print("gap gcd(gap,128) maxZeros minOut supportProduct")
    for row in rows[:16]:
        print(*row)
    assert rows[0][0] == 64
    assert rows[0][4] == 128
    print("PASS: exact two-sparse minimum support product is 128 at gap 64")


if __name__ == "__main__":
    main()
