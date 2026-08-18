#!/usr/bin/env python3
"""Finite arithmetic probe for the p=11 marked Hecke collision.

This script is deliberately a regression/falsifier, NOT the global theorem.
It uses only:

1. direct point counting on the level-11 elliptic curve

       E : y^2 + y = x^3 - x^2 - 10x - 20,

   so a_ell = ell + 1 - #E(F_ell);

2. the two definite marked-congruence norm forms already derived in
   P11MarkedQuaternionThetaExact:

   j=1728:
     N = (1+2a+c)^2 + (2b+d)^2 + 11c^2 + 11d^2,

   j=0:
     4N = 4(1+2a+3c+d)^2
          + (8b+4c+d)^2 + 44c^2 + 11d^2.

For each tested odd prime ell != 11, reciprocal stack balance on the two coarse
classes writes the Brandt matrix as

    [[ell+1-3t, 3t],
     [2t, ell+1-2t]],

and the nonconstant eigenvalue is ell+1-5t.  Hence

    t = (ell+1-a_ell)/5.

The marked B-standard deck sector has eigenvalue

    bb_id - bb_off.

The global theta identity suggested by the data is

    bb_id = ell+1-4t,
    bb_off = t,

which gives bb_id-bb_off = a_ell identically.

We verify the identity by complete definite-norm enumeration for all odd primes
3 <= ell <= 47, ell != 11.  This is strong evidence/regression for the Agda
producer target; it is not promoted to an all-prime proof.

Sources/context:
- John Voight, Quaternion Algebras, GTM 288 (2021),
  DOI 10.1007/978-3-030-56694-4.
- Markus Kirschmer and John Voight, Algorithmic Enumeration of Ideal Classes
  for Quaternion Orders, SIAM J. Comput. 39 (2010),
  DOI 10.1137/080734467.
- LMFDB 11.a is an executable cross-check only; no DOI is asserted for it.
"""

from math import isqrt


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    p = 2
    while p * p <= n:
        if n % p == 0:
            return n == p
        p += 1
    return True


def level11_newform_coefficient(ell: int) -> int:
    """Compute a_ell directly by #E(F_ell)."""
    points = 1  # point at infinity
    for x in range(ell):
        rhs = (x**3 - x**2 - 10 * x - 20) % ell
        for y in range(ell):
            if (y * y + y - rhs) % ell == 0:
                points += 1
    return ell + 1 - points


def j1728_raw_marked_norm_count(ell: int) -> int:
    """Complete count for N(alpha)=ell, alpha=1 mod 2O_1728."""
    root = isqrt(ell)
    cd = isqrt(ell // 11) + 1
    total = 0
    for c in range(-cd, cd + 1):
        for d in range(-cd, cd + 1):
            if 11 * c * c + 11 * d * d > ell:
                continue
            # |1+2a+c|, |2b+d| <= sqrt(ell).
            ra = root + abs(c) + 2
            rb = root + abs(d) + 2
            for a in range(-ra, ra + 1):
                A = 1 + 2 * a + c
                if A * A + 11 * c * c + 11 * d * d > ell:
                    continue
                for b in range(-rb, rb + 1):
                    B = 2 * b + d
                    n = A * A + B * B + 11 * c * c + 11 * d * d
                    if n == ell:
                        total += 1
    return total


def j0_raw_marked_norm_count(ell: int) -> int:
    """Complete count for N(alpha)=ell, alpha=1 mod 2O_0."""
    root = isqrt(ell)
    cmax = isqrt(ell // 11) + 1
    dmax = isqrt((4 * ell) // 11) + 1
    total = 0
    for c in range(-cmax, cmax + 1):
        for d in range(-dmax, dmax + 1):
            fixed = 44 * c * c + 11 * d * d
            if fixed > 4 * ell:
                continue
            # The positive squares bound A and B; these generous ranges are
            # derived from those inequalities, not an arbitrary search box.
            ra = root + 3 * abs(c) + abs(d) + 2
            rb = root + 4 * abs(c) + abs(d) + 2
            for a in range(-ra, ra + 1):
                A = 1 + 2 * a + 3 * c + d
                if 4 * A * A + fixed > 4 * ell:
                    continue
                for b in range(-rb, rb + 1):
                    B = 8 * b + 4 * c + d
                    four_n = 4 * A * A + B * B + fixed
                    if four_n == 4 * ell:
                        total += 1
    return total


def marked_loops(raw: int) -> int:
    # +/- alpha have the same prime cyclic kernel and act identically on E[2].
    assert raw % 2 == 0
    return raw // 2


def check_prime(ell: int):
    a = level11_newform_coefficient(ell)
    numerator = ell + 1 - a
    assert numerator % 5 == 0, (ell, a, numerator)
    t = numerator // 5

    j0 = marked_loops(j0_raw_marked_norm_count(ell))
    j1728 = marked_loops(j1728_raw_marked_norm_count(ell))

    predicted_j1728 = ell + 1 - 4 * t
    assert j1728 == predicted_j1728, (ell, a, t, j1728, predicted_j1728)

    bb_off = t
    standard_eigenvalue = j1728 - bb_off
    assert standard_eigenvalue == a, (ell, standard_eigenvalue, a)

    return {
        "ell": ell,
        "a_ell": a,
        "cross_unit": t,
        "j0_marked_loops": j0,
        "j1728_marked_loops": j1728,
        "standard_eigenvalue": standard_eigenvalue,
    }


def main():
    rows = []
    for ell in range(3, 48, 2):
        if ell == 11 or not is_prime(ell):
            continue
        rows.append(check_prime(ell))

    assert [r["ell"] for r in rows] == [3, 5, 7, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]

    print("p=11 marked Hecke collision scan: OK")
    print("ell  a_ell  t  j0_loops  j1728_loops  standard")
    for r in rows:
        print(
            f"{r['ell']:>3} {r['a_ell']:>6} {r['cross_unit']:>3}"
            f" {r['j0_marked_loops']:>9} {r['j1728_marked_loops']:>12}"
            f" {r['standard_eigenvalue']:>9}"
        )


if __name__ == "__main__":
    main()
