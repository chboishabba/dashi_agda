#!/usr/bin/env python3
"""Independent finite audit for PrimeFrickeGenusControlExact.agda.

The audit does not read Ogg labels while computing the modular column.  It:

1. enumerates primitive reduced positive-definite binary quadratic forms of
   discriminant -4p and, where p == 3 mod 4, discriminant -p;
2. recomputes the prime-level genus of X_0(p) from elliptic-point counts;
3. recomputes the Fricke fixed-point count from the two class numbers;
4. applies Riemann-Hurwitz to obtain genus X_0^+(p);
5. parses the Agda table and compares every finite datum.

Standard library only.  No Agda, Sage, PARI, network, or CI invocation.
"""

from __future__ import annotations

import math
import pathlib
import re
import sys
from dataclasses import dataclass
from typing import Dict, Iterable, List, Tuple

ROOT = pathlib.Path(__file__).resolve().parents[1]
AGDA = ROOT / "DASHI/Moonshine/PrimeFrickeGenusControlExact.agda"

PRIMES = [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71]
OGG_ODD = {3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71}


@dataclass(frozen=True)
class Row:
    p: int
    e2: int
    e3: int
    g0: int
    h4: int
    hp: int
    fixed: int
    gplus: int


def primitive_reduced_forms(discriminant: int) -> List[Tuple[int, int, int]]:
    """Enumerate primitive reduced positive-definite forms [a,b,c].

    For D < 0, reduced means |b| <= a <= c, with b >= 0 when either
    |b| = a or a = c.  Primitive means gcd(a,b,c)=1.
    """
    if discriminant >= 0 or discriminant % 4 not in (0, 1):
        raise ValueError(f"invalid negative quadratic discriminant {discriminant}")

    forms: List[Tuple[int, int, int]] = []
    # For a reduced positive-definite form, a <= sqrt(|D|/3).
    max_a = math.isqrt(abs(discriminant) // 3) + 2
    for a in range(1, max_a + 1):
        for b in range(-a, a + 1):
            numerator = b * b - discriminant
            denominator = 4 * a
            if numerator % denominator:
                continue
            c = numerator // denominator
            if a > c:
                continue
            if math.gcd(math.gcd(a, abs(b)), c) != 1:
                continue
            if (abs(b) == a or a == c) and b < 0:
                continue
            forms.append((a, b, c))
    return forms


def class_number(discriminant: int) -> int:
    return len(primitive_reduced_forms(discriminant))


def elliptic_counts(p: int) -> Tuple[int, int]:
    # Prime-level counts for X_0(p), with the small p=3 exceptional order-3
    # value kept explicit.
    e2 = 2 if p % 4 == 1 else 0
    if p == 3:
        e3 = 1
    else:
        e3 = 2 if p % 3 == 1 else 0
    return e2, e3


def compute_row(p: int) -> Row:
    e2, e3 = elliptic_counts(p)
    genus_numerator = p + 1 - 3 * e2 - 4 * e3
    assert genus_numerator >= 0 and genus_numerator % 12 == 0
    g0 = genus_numerator // 12

    h4 = class_number(-4 * p)
    hp = class_number(-p) if p % 4 == 3 else 0
    fixed = h4 + hp

    hurwitz_numerator = 2 * g0 + 2 - fixed
    assert hurwitz_numerator >= 0 and hurwitz_numerator % 4 == 0
    gplus = hurwitz_numerator // 4
    return Row(p, e2, e3, g0, h4, hp, fixed, gplus)


def parse_agda_rows() -> Dict[int, Row]:
    text = AGDA.read_text(encoding="utf-8")
    pattern = re.compile(
        r"frickeRow Matrix\.prime(\d+) =\s*\n"
        r"\s*prime-fricke-genus-row Matrix\.prime\1 "
        r"(\d+) refl (\d+) (\d+) (\d+) (\d+) (\d+) (\d+) (\d+) refl refl refl",
        re.MULTILINE,
    )
    rows: Dict[int, Row] = {}
    for match in pattern.finditer(text):
        constructor_p = int(match.group(1))
        level, e2, e3, g0, h4, hp, fixed, gplus = map(int, match.groups()[1:])
        if level != constructor_p:
            raise AssertionError(f"prime{constructor_p} stores level={level}")
        rows[constructor_p] = Row(level, e2, e3, g0, h4, hp, fixed, gplus)
    if set(rows) != set(PRIMES):
        raise AssertionError(
            f"Agda Fricke table prime mismatch: missing={sorted(set(PRIMES)-set(rows))}, "
            f"extra={sorted(set(rows)-set(PRIMES))}"
        )
    return rows


def main() -> int:
    agda_rows = parse_agda_rows()
    computed = {p: compute_row(p) for p in PRIMES}

    for p in PRIMES:
        if agda_rows[p] != computed[p]:
            raise AssertionError(
                f"p={p}: Agda={agda_rows[p]} computed={computed[p]}"
            )

    zero_locus = {p for p, row in computed.items() if row.gplus == 0}
    if zero_locus != OGG_ODD:
        raise AssertionError(
            f"Fricke genus-zero locus mismatch: got={sorted(zero_locus)} "
            f"expected={sorted(OGG_ODD)}"
        )

    positive = {p: computed[p].gplus for p in PRIMES if computed[p].gplus > 0}
    expected_positive = {37: 1, 43: 1, 53: 1, 61: 1, 67: 2}
    if positive != expected_positive:
        raise AssertionError(f"positive Fricke genera mismatch: {positive}")

    print("Prime Fricke genus control audit: OK")
    print("  19 odd prime rows agree with reduced-form class-number enumeration")
    print("  genus-zero locus:", sorted(zero_locus))
    print("  positive controls:", positive)
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (AssertionError, ValueError) as exc:
        print(f"Prime Fricke genus control audit FAILED: {exc}", file=sys.stderr)
        raise SystemExit(1)
