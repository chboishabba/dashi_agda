#!/usr/bin/env python3
"""Audit the Round-9 SO(3) -> finite-group restriction tables.

This script is intentionally independent of Agda normalization.  It parses the
three checked-in branching tables, recomputes their multiplicities from finite
character inner products, and verifies the regular-representation shift laws
and explicit Ogg/non-Ogg controls used by the no-go theorems.

It uses only Python's standard library and does not invoke CI or Agda.
"""

from __future__ import annotations

import pathlib
import re
import sys
from dataclasses import dataclass
from typing import Dict, Iterable, Tuple

ROOT = pathlib.Path(__file__).resolve().parents[1]

D4_PATH = ROOT / "DASHI/Foundations/D4SO3RestrictionJ0To35Exact.agda"
S4_PATH = ROOT / "DASHI/Foundations/OctahedralSO3RestrictionJ0To35Exact.agda"
A5_PATH = ROOT / "DASHI/Foundations/IcosahedralSO3RestrictionJ0To35Exact.agda"

OGG = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71}


def chi_pi(j: int) -> int:
    return 1 if j % 2 == 0 else -1


def chi_third(j: int) -> int:
    return (1, 0, -1)[j % 3]


def chi_quarter(j: int) -> int:
    return (1, 1, -1, -1)[j % 4]


@dataclass(frozen=True)
class PhiInt:
    """a + b*phi with phi^2 = phi + 1."""

    a: int
    b: int

    def __add__(self, other: "PhiInt") -> "PhiInt":
        return PhiInt(self.a + other.a, self.b + other.b)

    def __mul__(self, other: "PhiInt") -> "PhiInt":
        return PhiInt(
            self.a * other.a + self.b * other.b,
            self.a * other.b + self.b * other.a + self.b * other.b,
        )

    def scale(self, n: int) -> "PhiInt":
        return PhiInt(n * self.a, n * self.b)


P0 = PhiInt(0, 0)
PHI = PhiInt(0, 1)
PHI_CONJ = PhiInt(1, -1)


def chi_fifth(j: int) -> PhiInt:
    # theta = 2*pi/5
    return (
        PhiInt(1, 0),
        PHI,
        P0,
        PhiInt(0, -1),
        PhiInt(-1, 0),
    )[j % 5]


def chi_fifth_squared(j: int) -> PhiInt:
    # theta = 4*pi/5
    return (
        PhiInt(1, 0),
        PHI_CONJ,
        P0,
        PhiInt(-1, 1),
        PhiInt(-1, 0),
    )[j % 5]


def parse_table(path: pathlib.Path, constructor: str, width: int) -> Dict[int, Tuple[int, ...]]:
    text = path.read_text(encoding="utf-8")
    pattern = re.compile(
        rf"^branchingSpectrum Spin\.j(\d+) = {re.escape(constructor)} "
        + r"(\d+) " * (width - 1)
        + r"(\d+)$",
        re.MULTILINE,
    )
    table: Dict[int, Tuple[int, ...]] = {}
    for match in pattern.finditer(text):
        j = int(match.group(1))
        table[j] = tuple(int(match.group(i)) for i in range(2, 2 + width))
    if set(table) != set(range(36)):
        missing = sorted(set(range(36)) - set(table))
        extra = sorted(set(table) - set(range(36)))
        raise AssertionError(f"{path}: expected j=0..35; missing={missing}, extra={extra}")
    return table


def expected_d4(j: int) -> Tuple[int, ...]:
    # classes: 1, r^2, {r,r^3}, axis half-turns, diagonal half-turns
    sizes = (1, 1, 2, 2, 2)
    chi = (2 * j + 1, chi_pi(j), chi_quarter(j), chi_pi(j), chi_pi(j))
    irreps = (
        (1, 1, 1, 1, 1),
        (1, 1, 1, -1, -1),
        (1, 1, -1, 1, -1),
        (1, 1, -1, -1, 1),
        (2, -2, 0, 0, 0),
    )
    return tuple(sum(s * c * r for s, c, r in zip(sizes, chi, row)) // 8 for row in irreps)


def expected_s4(j: int) -> Tuple[int, ...]:
    # classes: identity, edge half-turn, face half-turn, third-turn, quarter-turn
    sizes = (1, 6, 3, 8, 6)
    chi = (2 * j + 1, chi_pi(j), chi_pi(j), chi_third(j), chi_quarter(j))
    irreps = (
        (1, 1, 1, 1, 1),       # A1
        (1, -1, 1, 1, -1),     # A2
        (2, 0, 2, -1, 0),      # E
        (3, -1, -1, 0, 1),     # T1
        (3, 1, -1, 0, -1),     # T2
    )
    return tuple(sum(s * c * r for s, c, r in zip(sizes, chi, row)) // 24 for row in irreps)


def expected_a5(j: int) -> Tuple[int, ...]:
    sizes = (1, 15, 20, 12, 12)
    chi = (
        PhiInt(2 * j + 1, 0),
        PhiInt(chi_pi(j), 0),
        PhiInt(chi_third(j), 0),
        chi_fifth(j),
        chi_fifth_squared(j),
    )
    irreps = (
        (PhiInt(1, 0), PhiInt(1, 0), PhiInt(1, 0), PhiInt(1, 0), PhiInt(1, 0)),
        (PhiInt(3, 0), PhiInt(-1, 0), P0, PHI, PHI_CONJ),
        (PhiInt(3, 0), PhiInt(-1, 0), P0, PHI_CONJ, PHI),
        (PhiInt(4, 0), P0, PhiInt(1, 0), PhiInt(-1, 0), PhiInt(-1, 0)),
        (PhiInt(5, 0), PhiInt(1, 0), PhiInt(-1, 0), P0, P0),
    )
    out = []
    for row in irreps:
        total = P0
        for size, source, target in zip(sizes, chi, row):
            total = total + (source * target).scale(size)
        if total.b != 0 or total.a % 60 != 0:
            raise AssertionError(f"A5 inner product failed integrality at j={j}: {total}")
        out.append(total.a // 60)
    return tuple(out)


def check_table(name: str, actual: Dict[int, Tuple[int, ...]], expected) -> None:
    for j in range(36):
        wanted = expected(j)
        if actual[j] != wanted:
            raise AssertionError(f"{name} j={j}: actual={actual[j]} expected={wanted}")


def add(a: Tuple[int, ...], b: Tuple[int, ...]) -> Tuple[int, ...]:
    return tuple(x + y for x, y in zip(a, b))


def scale(n: int, a: Tuple[int, ...]) -> Tuple[int, ...]:
    return tuple(n * x for x in a)


def check_shift(table: Dict[int, Tuple[int, ...]], period: int, regular: Tuple[int, ...]) -> None:
    for j in range(36 - period):
        if table[j + period] != add(table[j], regular):
            raise AssertionError(
                f"regular shift period={period} failed at j={j}: "
                f"{table[j + period]} != {add(table[j], regular)}"
            )


def dimension(vector: Tuple[int, ...], dims: Tuple[int, ...]) -> int:
    return sum(m * d for m, d in zip(vector, dims))


def main() -> int:
    d4 = parse_table(D4_PATH, "d4-spectrum", 5)
    s4 = parse_table(S4_PATH, "oct-spectrum", 5)
    a5 = parse_table(A5_PATH, "ico-spectrum", 5)

    check_table("D4", d4, expected_d4)
    check_table("S4", s4, expected_s4)
    check_table("A5", a5, expected_a5)

    for j in range(36):
        assert dimension(d4[j], (1, 1, 1, 1, 2)) == 2 * j + 1
        assert dimension(s4[j], (1, 1, 2, 3, 3)) == 2 * j + 1
        assert dimension(a5[j], (1, 3, 3, 4, 5)) == 2 * j + 1

    d4_reg = (1, 1, 1, 1, 2)
    s4_reg = (1, 1, 2, 3, 3)
    a5_reg = (1, 3, 3, 4, 5)
    check_shift(d4, 4, d4_reg)
    check_shift(s4, 12, s4_reg)
    check_shift(a5, 30, a5_reg)

    assert d4[4] == add(d4[0], d4_reg) == (2, 1, 1, 1, 2)
    assert s4[26] == add(s4[2], scale(2, s4_reg))
    assert a5[33] == add(a5[3], a5_reg)

    assert 5 in OGG and 7 in OGG
    assert 9 not in OGG and 53 not in OGG and 67 not in OGG

    print("Ogg representation-reduction audit: OK")
    print("  36 D4 rows = exact character inner products")
    print("  36 S4 rows = exact character inner products")
    print("  36 A5 rows = exact Z[phi] character inner products")
    print("  regular shifts: D4 +4, S4 +12, A5 +30")
    print("  controls: 9, 53, 67 are non-Ogg; 5, 7 are Ogg")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except AssertionError as exc:
        print(f"Ogg representation-reduction audit FAILED: {exc}", file=sys.stderr)
        raise SystemExit(1)
