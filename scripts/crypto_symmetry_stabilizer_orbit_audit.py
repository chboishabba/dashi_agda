#!/usr/bin/env python3
"""Blue-team symmetry audit for the ML-KEM ring relation.

This is a discovery script, not a proof and not an attack implementation.
It tests the symmetry-first question suggested by the SSP formalization:
which natural ring actions preserve the prior/score structure, and which of
those survive as stabilizers of a fixed public instance?

The action family used here is the cyclotomic Galois action
    sigma_a : X -> X^a,  a odd mod 512,
on R_q = Z_q[X]/(X^256+1), together with monomial units ±X^r.

The important distinction is:
  * family equivariance: transform A,t,s,e together;
  * fixed-instance symmetry: hold A,t fixed and transform only hidden states.
Only the latter could directly quotient a fixed-instance recovery problem.
"""

from __future__ import annotations

import argparse
import random
from collections import Counter

import numpy as np

Q = 3329
N = 256
ODD_UNITS = tuple(range(1, 2 * N, 2))


def centered_mod(x: np.ndarray) -> np.ndarray:
    y = np.asarray(x, dtype=np.int64) % Q
    return np.where(y > Q // 2, y - Q, y)


def sigma_a(poly: np.ndarray, a: int) -> np.ndarray:
    """Apply X -> X^a in Z_q[X]/(X^256+1)."""
    out = np.zeros(N, dtype=np.int64)
    p = np.asarray(poly, dtype=np.int64) % Q
    for j, c in enumerate(p):
        e = (a * j) % (2 * N)
        if e >= N:
            out[e - N] = (out[e - N] - int(c)) % Q
        else:
            out[e] = (out[e] + int(c)) % Q
    return out


def monomial_unit(poly: np.ndarray, r: int, sign: int) -> np.ndarray:
    """Multiply by sign*X^r in R_q."""
    out = np.zeros(N, dtype=np.int64)
    p = np.asarray(poly, dtype=np.int64) % Q
    for j, c in enumerate(p):
        e = j + r
        pos = e % N
        val = int(c)
        if (e // N) % 2:
            val = -val
        out[pos] = (out[pos] + sign * val) % Q
    return out


def ring_mul(a: np.ndarray, b: np.ndarray) -> np.ndarray:
    conv = np.convolve(np.asarray(a, dtype=np.int64), np.asarray(b, dtype=np.int64))
    out = conv[:N].copy()
    tail = conv[N:]
    out[: len(tail)] -= tail  # X^256 = -1
    return out % Q


def cbd2_like(rng: random.Random) -> np.ndarray:
    # Support-faithful structural carrier. This is not a probability sampler for
    # the exact centered-binomial weights; the symmetry tests only need the
    # sign/permutation-invariant support and shell quantities below.
    return np.array([rng.randrange(-2, 3) for _ in range(N)], dtype=np.int64) % Q


def uniform_poly(rng: random.Random) -> np.ndarray:
    return np.array([rng.randrange(Q) for _ in range(N)], dtype=np.int64)


def prior_shell_signature(poly: np.ndarray) -> tuple:
    x = centered_mod(poly)
    abs_hist = Counter(map(int, np.abs(x)))
    return (
        tuple(abs_hist.get(v, 0) for v in (0, 1, 2)),
        int(np.abs(x).sum()),
        int((x * x).sum()),
        int(np.abs(x).max()),
        bool(np.all((x >= -2) & (x <= 2))),
    )


def residual_score(a: np.ndarray, t: np.ndarray, s: np.ndarray) -> int:
    e = centered_mod((t - ring_mul(a, s)) % Q)
    return int(e @ e)


def galois_stabilizer(poly: np.ndarray) -> list[int]:
    return [a for a in ODD_UNITS if np.array_equal(sigma_a(poly, a), poly)]


def monomial_stabilizer(poly: np.ndarray) -> list[tuple[int, int]]:
    out = []
    for r in range(N):
        for sign in (1, -1):
            if np.array_equal(monomial_unit(poly, r, sign), poly):
                out.append((r, sign))
    return out


def audit(seed: int, trials: int) -> None:
    rng = random.Random(seed)

    # 1. Generic exact stabilizers.
    for label, sampler in (("uniform-public", uniform_poly), ("CBD2-hidden", cbd2_like)):
        gst = []
        mst = []
        for _ in range(trials):
            p = sampler(rng)
            gst.append(len(galois_stabilizer(p)))
            mst.append(len(monomial_stabilizer(p)))
        print(
            f"{label}: galois stabilizer mean={sum(gst)/len(gst):.3f}, "
            f"max={max(gst)}; monomial stabilizer mean={sum(mst)/len(mst):.3f}, max={max(mst)}"
        )

    # 2. Generic CBD-like hidden orbit and prior-shell invariance.
    orbit_sizes = []
    shell_violations = 0
    shell_tests = 0
    for _ in range(trials):
        s = cbd2_like(rng)
        orbit = {tuple(sigma_a(s, a).tolist()) for a in ODD_UNITS}
        orbit_sizes.append(len(orbit))
        sig = prior_shell_signature(s)
        for a in rng.sample(list(ODD_UNITS), min(20, len(ODD_UNITS))):
            shell_tests += 1
            if prior_shell_signature(sigma_a(s, a)) != sig:
                shell_violations += 1
    print(
        f"CBD2-like Galois orbit mean={sum(orbit_sizes)/len(orbit_sizes):.3f}, "
        f"min={min(orbit_sizes)}, max={max(orbit_sizes)}"
    )
    print(f"prior-shell invariance violations={shell_violations}/{shell_tests}")

    # 3. Family equivariance of the ring equation, and score covariance.
    equivariance_failures = 0
    fixed_score_equal = 0
    transported_score_equal = 0
    score_tests = 0

    a_pub = uniform_poly(rng)
    s_true = cbd2_like(rng)
    e_true = cbd2_like(rng)
    t_pub = (ring_mul(a_pub, s_true) + e_true) % Q

    for _ in range(trials * 2):
        g = rng.choice(ODD_UNITS)
        cand = cbd2_like(rng)

        lhs = sigma_a(ring_mul(a_pub, cand), g)
        rhs = ring_mul(sigma_a(a_pub, g), sigma_a(cand, g))
        if not np.array_equal(lhs, rhs):
            equivariance_failures += 1

        score = residual_score(a_pub, t_pub, cand)
        fixed_score = residual_score(a_pub, t_pub, sigma_a(cand, g))
        transported_score = residual_score(
            sigma_a(a_pub, g), sigma_a(t_pub, g), sigma_a(cand, g)
        )
        score_tests += 1
        fixed_score_equal += int(fixed_score == score)
        transported_score_equal += int(transported_score == score)

    print(f"ring-equivariance failures={equivariance_failures}/{score_tests}")
    print(f"fixed-public score preserved={fixed_score_equal}/{score_tests}")
    print(f"transported-instance score preserved={transported_score_equal}/{score_tests}")

    # Boundary statement for the empirical audit.
    print("\nInterpretation boundary:")
    print("  natural cyclotomic symmetries are large on the instance family and prior shells,")
    print("  but generic sampled public/hidden objects have only the identity exact stabilizer.")
    print("  Therefore family equivariance alone does not quotient a generic fixed-instance search.")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--seed", type=int, default=20260815)
    parser.add_argument("--trials", type=int, default=20)
    args = parser.parse_args()
    audit(args.seed, args.trials)


if __name__ == "__main__":
    main()
