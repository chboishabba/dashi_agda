#!/usr/bin/env python3
"""Independent finite parity probe for Eisenstein norm-shell counting.

This script is not theorem authority.  It independently compares

  #{(a,b) in Z^2 : a^2-a*b+b^2=n}

against

  6 * sum_{d|n} chi_{-3}(d)

for a requested finite prefix.  The geometric search bound is justified by
the symbolic identity owned in Agda/Lean:

  4 Q(a,b) = 3 a^2 + (a-2b)^2,

and its symmetric b-version.
"""

import argparse
import math


def chi3(d: int) -> int:
    residue = d % 3
    if residue == 1:
        return 1
    if residue == 2:
        return -1
    return 0


def divisor_shell(n: int) -> int:
    total = 0
    for d in range(1, math.isqrt(n) + 1):
        if n % d == 0:
            total += chi3(d)
            partner = n // d
            if partner != d:
                total += chi3(partner)
    return 6 * total


def geometric_shell(n: int) -> int:
    # Coercivity gives 3*a^2 <= 4*n and symmetrically 3*b^2 <= 4*n.
    # The +2 is deliberately conservative and keeps this probe independent
    # of any delicate integer-square-root boundary convention.
    bound = math.isqrt((4 * n) // 3) + 2
    count = 0
    for a in range(-bound, bound + 1):
        for b in range(-bound, bound + 1):
            if a * a - a * b + b * b == n:
                count += 1
    return count


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--limit", type=int, default=1000)
    args = parser.parse_args()

    mismatches = []
    for n in range(1, args.limit + 1):
        geometric = geometric_shell(n)
        divisor = divisor_shell(n)
        if geometric != divisor:
            mismatches.append((n, geometric, divisor))

    if mismatches:
        print("FAIL", mismatches[:20])
        raise SystemExit(1)

    print(
        "PASS: geometric and chi_-3 divisor shell counts agree "
        f"for n=1..{args.limit}"
    )
    print("first 20:", [geometric_shell(n) for n in range(1, 21)])


if __name__ == "__main__":
    main()
