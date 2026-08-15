#!/usr/bin/env python3
"""Blue-team ML-KEM symmetry / uncertainty discovery probe.

This script is exploratory, not a security claim.  It studies two structural
questions suggested by the SSP symmetry lane:

1. How quickly does a generic public ring element break the natural odd
   cyclotomic action X -> X^a, a in (Z/512Z)^x?
2. Does one FIPS-203 parity NTT block exhibit the expected support tradeoff
   between coefficient localisation and residue localisation?

The output is intended to guide later Agda theorem selection, not to replace a
proof or to claim an ML-KEM attack.
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


def sigma(poly: np.ndarray, a: int) -> np.ndarray:
    out = np.zeros(N, dtype=np.int64)
    for j, c in enumerate(np.asarray(poly, dtype=np.int64) % Q):
        e = (a * j) % (2 * N)
        if e >= N:
            out[e - N] = (out[e - N] - int(c)) % Q
        else:
            out[e] = (out[e] + int(c)) % Q
    return out


def parity_ntt_matrix() -> np.ndarray:
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


def exact_two_sparse_extremizers(w: np.ndarray) -> list[tuple[int, int, int, int]]:
    # For x=e_a+c e_b with d=b-a, zeros satisfy gamma_i^d=-1/c.
    # Thus the largest possible zero set for gap d is exactly the largest fibre
    # of i -> gamma_i^d over the 128 FIPS quadratic residues.
    rows = []
    gammas = [gamma(i) for i in range(HALF)]
    for d in range(1, HALF):
        fibres = Counter(pow(g, d, Q) for g in gammas)
        max_zeros = max(fibres.values())
        min_out = HALF - max_zeros
        rows.append((d, math.gcd(d, HALF), max_zeros, 2 * min_out))
    return rows


def main() -> None:
    rng = random.Random(20260815)
    w = parity_ntt_matrix()

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
            y = (w @ x) % Q
            outs.append(support(y))
            products.append(k * support(y))
        print(
            f"k={k:3d} mean_out={sum(outs)/len(outs):8.3f} "
            f"min_out={min(outs):3d} min_product={min(products):5d}"
        )
    print()

    rows = exact_two_sparse_extremizers(w)
    rows.sort(key=lambda r: (r[3], r[0]))
    print("exact two-sparse extrema (gap, gcd(gap,128), max zeros, support product)")
    for row in rows[:16]:
        print(row)
    print("minimum exact two-sparse product:", rows[0][3])


if __name__ == "__main__":
    main()
