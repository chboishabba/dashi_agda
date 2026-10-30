#!/usr/bin/env python3
"""Finite regression for CT11->M15 numeric support, NOT Agda kernel evidence.

Original theorem owners: RiemannVonMangoldtSpecification,
TwinPrimeMangoldtErrorSupportProperExact and the CT11 finite image.
No prime gap, logarithmic growth or analytic positivity is inferred.
"""
from math import isqrt


def primes_to(limit: int) -> list[int]:
    sieve = bytearray(b"\x01") * (limit + 1)
    sieve[0:2] = b"\x00\x00"
    for p in range(2, isqrt(limit) + 1):
        if sieve[p]:
            sieve[p * p : limit + 1 : p] = b"\x00" * (
                (limit - p * p) // p + 1
            )
    return [p for p in range(2, limit + 1) if sieve[p]]


def genuine_proper_prime_powers(limit: int) -> set[int]:
    out: set[int] = set()
    for p in primes_to(isqrt(limit)):
        v = p * p
        while v <= limit:
            out.add(v)
            v *= p
    return out


def candidate_image(limit: int) -> set[int]:
    if limit == 0:
        return set()
    exponent_cutoff = limit.bit_length() - 1
    # The Agda enumeration includes base=1, and exponent index e-2.
    # E indices are deliberately conservative: actual exponents 2..E+1.
    return {
        base**exp
        for base in range(1, isqrt(limit) + 1)
        for exp in range(2, exponent_cutoff + 2)
    }


def main() -> None:
    upper_max = 2048
    true_values = genuine_proper_prime_powers(upper_max)
    supported_pairs = pair_checks = 0
    for upper in range(4, upper_max + 1):
        values = candidate_image(upper)
        assert len(values) <= isqrt(upper) * (upper.bit_length() - 1)
        assert all(p in values for p in true_values if p <= upper)
        support_in_window = 0
        for n in range(0, upper - 1):
            pair_checks += 1
            has_proper = n in true_values or n + 2 in true_values
            if has_proper:
                support_in_window += 1
                supported_pairs += 1
                assert n in values or n + 2 in values
        # Each proper-power VALUE can occur in at most two shifted
        # positions: as left or right endpoint. This is a numeric model
        # of the pending finite injection/cardinality proof.
        assert support_in_window <= 2 * sum(
            p <= upper for p in true_values
        )
    image36 = candidate_image(36)
    assert 36 in image36 and 36 not in true_values
    assert 1 in image36 and max(image36) > 36
    print(
        f"PASS U=4..{upper_max}: {pair_checks:,} shifted pairs, "
        f"{supported_pairs:,} proper-power-support pairs; "
        "no missed support; composite-base/out-of-range overcount confirmed"
    )


if __name__ == "__main__":
    main()
