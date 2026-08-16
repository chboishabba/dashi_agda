#!/usr/bin/env python3
"""Compact blue-team certificate for the m=8 raw FIPS pair (0,3).

Primary cryptographic source:
  NIST, Module-Lattice-Based Key-Encapsulation Mechanism Standard, FIPS 203,
  2024. DOI: 10.6028/NIST.FIPS.203.

This script does *not* replay the 5^8 = 390625 secret enumeration.  It reduces
raw-pair injectivity to a 4+4 difference-kernel certificate.

For two CBD2 vectors x,y, each difference d_j=x_j-y_j lies in [-4,4].  For the
actual FIPS evaluation points

    a = gamma_0 = 17,
    b = gamma_3 = 568,

we have

    a^4 = b^4 = 296 (mod 3329).

Therefore group coordinates j and j+4:

    e_j = d_j + 296 d_{j+4},  j=0,1,2,3.

Each e_j belongs to the 81-element set

    S = {u + 296 v (mod q) : u,v in [-4,4]}.

The representation is itself injective because the 81 residues are distinct.
The two zero-signature equations become one cubic E(X) with roots 17 and 568.
Since

    (X-17)(X-568) = X^2 - 585 X - 331  (mod 3329),

any such cubic kernel vector must satisfy, for p=e_2+585 e_3,

    e_0 = -331 p,
    e_1 = -585 p - 331 e_3                 (mod q).

Thus only (e_2,e_3) in S^2 must be checked: 81^2 = 6561 cases.  Exactly 161
survive the e_0-in-S filter, and exactly one survives both e_0,e_1 membership:
the all-zero pair.  This proves the bounded difference kernel is trivial once
the algebraic root-factor reduction is admitted.

This is a defensive leakage-resolution certificate.  It proves nothing about a
physical implementation exposing the raw pair, and it is not a whole-key or
runtime claim.
"""

from __future__ import annotations

from dataclasses import dataclass

Q = 3329
A = 17
B = 568
A4 = 296
CBD_DIFF = range(-4, 5)


@dataclass(frozen=True)
class CompressedDifference:
    low: int
    high: int
    residue: int


def compressed_support() -> tuple[CompressedDifference, ...]:
    return tuple(
        CompressedDifference(u, v, (u + A4 * v) % Q)
        for u in CBD_DIFF
        for v in CBD_DIFF
    )


def main() -> None:
    support = compressed_support()
    residues = {entry.residue for entry in support}

    assert len(support) == 81
    assert len(residues) == 81
    assert [entry for entry in support if entry.residue == 0] == [
        CompressedDifference(0, 0, 0)
    ]

    assert pow(A, 4, Q) == A4
    assert pow(B, 4, Q) == A4
    assert ((A + B) % Q) == 585
    assert (A * B) % Q == 2998  # -331 mod q

    e0_survivors = []
    full_survivors = []

    for e2_entry in support:
        for e3_entry in support:
            e2 = e2_entry.residue
            e3 = e3_entry.residue
            p = (e2 + 585 * e3) % Q
            e0 = (-331 * p) % Q
            e1 = (-585 * p - 331 * e3) % Q

            if e0 not in residues:
                continue
            e0_survivors.append((e2_entry, e3_entry, p, e0, e1))

            if e1 in residues:
                full_survivors.append((e2_entry, e3_entry, p, e0, e1))

    assert len(e0_survivors) == 161
    assert full_survivors == [
        (
            CompressedDifference(0, 0, 0),
            CompressedDifference(0, 0, 0),
            0,
            0,
            0,
        )
    ]

    print("ML-KEM/FIPS-203 pair (0,3) compact injectivity certificate")
    print(f"q={Q}, a={A}, b={B}, a^4=b^4={A4}")
    print("compressed coefficient support: 81 distinct residues")
    print("candidate reduced pairs: 81^2 = 6561")
    print(f"after e0-in-S filter: {len(e0_survivors)}")
    print(f"after e1-in-S filter: {len(full_survivors)}")
    print("unique survivor: e0=e1=e2=e3=0")
    print("interpretation: trivial bounded raw difference kernel only")
    print("boundary: no physical leakage / whole-key / runtime claim")


if __name__ == "__main__":
    main()
