#!/usr/bin/env python3
"""Exact-integer, independent K4 assay: level-32 eta product, Jacobi theta and E(Fp).

Only polynomial truncations and finite fields are tested. This is NOT a
formal proof of the infinite Jacobi identity, modularity, Mellin or BSD.
It uses no external packages, floats, internet, CI or invented a_p values.

For q=exp(2 pi i tau):
 eta(4 tau)^2 eta(8 tau)^2
 = q * product_{n>=1} (1-q^(4n))^2 (1-q^(8n))^2
 = (sum_{n>=0} (-1)^n(2n+1) q^((2n+1)^2))
   * (1 + 2 sum_{m>=1} (-1)^m q^(4m^2)).

The analytic infinite equality is the Jacobi-product bridge that must
be formalized separately. Exact finite agreement is useful regression.

See: https://seewoo5.github.io/jekyll/update/2025/10/02/explicit-modularity.html
Original E(Fp) witnesses: DASHI.Mathematics.Arithmetic.EllipticCurveSmallPrimeFrobeniusExact
"""
from __future__ import annotations

import argparse
import json
from math import isqrt
from pathlib import Path

ORIGINAL_FROBENIUS = {3: 0, 5: -2, 7: 0, 11: 0, 13: 6, 17: 2, 19: 0}


def eta_q_coefficients(cutoff: int) -> list[int]:
    if cutoff < 1:
        raise ValueError("cutoff must be >= 1")
    coefficients = [0] * (cutoff + 1)
    coefficients[1] = 1
    for scale in (4, 8):
        for n in range(1, cutoff // scale + 1):
            k = scale * n
            old = coefficients
            coefficients = old.copy()
            for j in range(cutoff + 1):
                if j >= k:
                    coefficients[j] -= 2 * old[j-k]
                if j >= 2*k:
                    coefficients[j] += old[j-2*k]
    return coefficients


def jacobi_gaussian_coefficients(cutoff: int) -> list[int]:
    output = [0] * (cutoff + 1)
    for n in range(isqrt(cutoff) // 2 + 1):
        odd = 2*n + 1
        if odd*odd > cutoff:
            break
        first_weight = (-1)**n * odd
        for m in range(isqrt(cutoff) // 2 + 1):
            exponent = odd*odd + 4*m*m
            if exponent > cutoff:
                break
            second_weight = 1 if m == 0 else 2 * (-1)**m
            output[exponent] += first_weight*second_weight
    return output


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    return all(n % d for d in range(2, isqrt(n) + 1))


def elliptic_trace_finite_field(p: int) -> int:
    if not is_prime(p) or p == 2:
        raise ValueError("need an odd prime")
    # Count y solutions to y^2 = x^3-x over F_p, including infinity.
    square_fibres = [0]*p
    for y in range(p):
        square_fibres[(y*y) % p] += 1
    count = 1 + sum(square_fibres[(x*x*x-x) % p] for x in range(p))
    return p+1-count


def assess(cutoff: int) -> dict:
    eta = eta_q_coefficients(cutoff)
    theta = jacobi_gaussian_coefficients(cutoff)
    mismatch = [(i, eta[i], theta[i]) for i in range(cutoff+1)
                if eta[i] != theta[i]]
    source = {p: {"repo_a_p": ap, "eta": eta[p], "theta": theta[p],
                  "independent_curve_count": elliptic_trace_finite_field(p)}
              for p, ap in ORIGINAL_FROBENIUS.items() if p <= cutoff}
    prime_mismatch = [
        (p, eta[p], elliptic_trace_finite_field(p))
        for p in range(3, cutoff + 1, 2) if is_prime(p)
        and eta[p] != elliptic_trace_finite_field(p)
    ]
    power_mismatch = [
        (p, eta[p*p], eta[p]**2-p)
        for p in range(3, isqrt(cutoff)+1, 2) if is_prime(p)
        and eta[p*p] != eta[p]**2-p
    ]
    result = {
        "curve": "y^2=x^3-x",
        "eta": "eta(4 tau)^2 eta(8 tau)^2",
        "integer_q_cutoff": cutoff,
        "all_coefficient_mismatches": mismatch[:20],
        "full_agreement": not mismatch,
        "original_checked_rows": source,
        "original_rows_agree": all(
            len(set(r.values())) == 1 for r in source.values()),
        "prime_count_crosschecked": sum(is_prime(p) for p in range(3, cutoff+1, 2)),
        "prime_trace_mismatches": prime_mismatch[:20],
        "prime_square_mismatches": power_mismatch[:20],
        "sample_coefficients": {
            str(k): eta[k] for k in
            (1, 5, 9, 13, 17, 25, 29, 37, 41, 49)
            if k <= cutoff},
        "kernel_accepted": False,
        "infinite_identity_proved": False,
        "mellin_identity_proved": False,
    }
    return result


def main() -> None:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--cutoff", type=int, default=256)
    p.add_argument("--output", type=Path)
    args = p.parse_args()
    report = assess(args.cutoff)
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(report, indent=2)+"\n")
    print(json.dumps(report, indent=2))
    if not (report["full_agreement"] and report["original_rows_agree"]
            and not report["prime_trace_mismatches"]
            and not report["prime_square_mismatches"]):
        raise SystemExit("FAILED: finite eta/Gaussian/elliptic exactness check")


if __name__ == "__main__":
    main()
