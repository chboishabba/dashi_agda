#!/usr/bin/env python3
"""Exact-rational control of the original SU(2) six-plaquette action reduction.

For actual SU(2) quaternion coordinates u and six oriented staples v_j:
 S=sum_j v_j; R=norm(S); D6=sum_j (1-u dot v_j)=6-u dot S.
 Cauchy--Schwarz gives D6 >= 6-R.

For 0<r<6, {R<r} implies 1 <= D6/(6-r) pointwise. Therefore
 P(R<r) <= E[D6]/(6-r) for EVERY original normalized Wilson Gibbs
 measure, without an independence assumption.

Combined with the existing one-link Haar tail (separately proved in
Docs/physics/YMClaySU2OriginalOneLinkCoherentStapleTail20261109.md):
 P(t(UV)<=0) <= E[D6]/(6-r) + 3 exp(-beta*r/2).

This is a deterministic finite-source regression, not an Agda kernel
proof, an estimate on E[D6], or spatial polymer clustering.
"""
from fractions import Fraction
from itertools import product

Q = [
    (Fraction(1), Fraction(0), Fraction(0), Fraction(0)),
    (Fraction(-1), Fraction(0), Fraction(0), Fraction(0)),
    (Fraction(0), Fraction(1), Fraction(0), Fraction(0)),
    (Fraction(0), Fraction(0), Fraction(1), Fraction(0)),
    (Fraction(3, 5), Fraction(4, 5), Fraction(0), Fraction(0)),
]
THRESHOLDS = (Fraction(1), Fraction(3), Fraction(5), Fraction(11, 2))


def dot(a, b):
    return sum((x*y for x,y in zip(a,b)), Fraction(0))


def verify(u, staples, r):
    s = tuple(sum((v[i] for v in staples), Fraction(0)) for i in range(4))
    norm_sq = dot(s, s)
    d = sum((1-dot(u,v) for v in staples), Fraction(0))
    assert d >= 0 and 0 < r < 6
    # Cauchy--Schwarz: (u dot S)^2 <= ||S||^2, exact rational.
    udots = dot(u,s)
    assert udots*udots <= norm_sq
    assert d == 6-udots
    # If R<r, the deterministic Markov witness D/(6-r)>=1.
    if norm_sq < r*r:
        assert d >= 6-r
    return norm_sq < r*r

def main():
    checked = 0
    frustrated = 0
    for six in product(Q, repeat=6):
        for u in (Q[0],Q[1],Q[4]):
            for r in THRESHOLDS:
                frustrated += int(verify(u, six, r))
                checked += 1
    assert checked == 5**6 * 3 * len(THRESHOLDS)
    print(f"PASS: {checked} rational SU(2) six-staple event/action checks; {frustrated} frustrated events")
    print("SCOPE: finite source Markov bridge ONLY; no E[D6] uniform bound or spatial Wilson covariance decay")

if __name__ == "__main__":
    main()
