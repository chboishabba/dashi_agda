#!/usr/bin/env python3
"""Independent exact-rational source control; NOT Agda kernel/Clay physics.

Checks only:
  - the correct 4^-n Cauchy tail coefficient;
  - linear vs nonlinear observables of a standard Gaussian (Wick);
  - existing source Cartan-Killing h^vee table and 11/24 algebraic floor.

The true original Wilson scale-local estimate, physical group measures,
gauge-invariant continuum N1 witness, and OS gap remain unproved.
"""
from fractions import Fraction as Q


def casimir(family, offset=0):
    assert offset >= 0
    if family == "A":
        return offset + 2
    if family == "B":
        return 2 * offset + 3
    if family == "C":
        return offset + 3
    if family == "D":
        return 2 * offset + 6
    return {"E6": 12, "E7": 18, "E8": 30,
            "F4": 9, "G2": 4}[family]


def gaussian_fourth_cumulant(mu1, mu2, mu3, mu4):
    return (mu4 - 4 * mu3 * mu1 - 3 * mu2 * mu2
            + 12 * mu2 * mu1 * mu1 - 6 * mu1 ** 4)


def main():
    # The attachment's formula (1/3)*4^-n misses a factor of 4.
    for n in range(18):
        geometric_tail = Q(4, 3) * Q(1, 4 ** n)
        assert geometric_tail == Q(4, 3 * 4 ** n)
        for count in range(15):
            finite = sum((Q(1, 4 ** k) for k in range(n, n + count)), Q(0))
            closed = geometric_tail * (1 - Q(1, 4 ** count))
            assert finite == closed
            assert finite <= geometric_tail
    assert Q(4, 3) * Q(1, 4) == Q(1, 3)  # sum from k=1
    assert Q(1, 3) != Q(1, 3) * Q(1, 4)  # false old tail formula

    # The fixed raw Gaussian/Wick moments are standard classical inputs.
    linear = gaussian_fourth_cumulant(Q(0), Q(1), Q(0), Q(3))
    square = gaussian_fourth_cumulant(Q(1), Q(3), Q(15), Q(105))
    assert linear == 0 and square == 48

    sources = 0
    for family in ("A", "B", "C", "D"):
        for n in range(1024):
            ca = casimir(family, n)
            assert ca >= 2
            assert Q(ca) * Q(11, 24) >= Q(11, 12)
            sources += 1
    for group in ("E6", "E7", "E8", "F4", "G2"):
        ca = casimir(group)
        assert ca >= 2
        assert Q(ca) * Q(11, 24) >= Q(11, 12)
        sources += 1

    print(f"PASS: 18x15 exact finite 4^-k tails, true 4/3 coefficient")
    print("PASS: linear Gaussian fourth cumulant 0; quadratic observable 48")
    print(f"PASS: {sources} classified Lie-family coefficient samples")
    print("REUSED: existing CompactSimpleUniversalBetaFloorExact has the forall-family proof")
    print("OPEN: true Wilson 4^-k step estimate; source physical N1 and G1 analytic inputs")


if __name__ == "__main__":
    main()
