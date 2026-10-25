#!/usr/bin/env python3
"""Same-topology / different-clopen-measure theorem for two Cantor products.

Source: elementary clopen-cylinder measure and finite prefix coding.
Existing mathematical owners reused:
  DASHI/Foundations/CantorProjectiveCylinderMeasureExact.agda
  DASHI/Mathematics/Topology/ExoticBinaryTernaryPantsCodecExact.agda
  DASHI/Mathematics/Topology/AlexanderHornedBinaryTernaryExistingCodecWeldExact.agda
  dashi_lean4 PR #86 CompatibleCantorTower (set equivalence; no topological
  homeomorphism has been kernel-verified).

THEOREM ON STANDARD PRODUCT TOPOLOGIES: no measure-preserving
homeomorphism exists from fair-bit binary Cantor measure to uniform
three-symbol Bernoulli Cantor measure.

Proof (mathematics, not machine theorem):
  Let C be the cylinder "first ternary digit = 3". Its uniform ternary
  measure is 1/3 and it is clopen. Under a homeomorphism h from the
  binary Cantor product onto the ternary product, h^-1(C) is clopen.
  Compactness and the cylinder basis imply every binary clopen set
  is a FINITE union of same-depth binary cylinders. Its fair-bit
  measure is therefore k/2^n for some integers k,n>=0.
  k/2^n = 1/3 implies 3k=2^n, impossible modulo 3
  since 2^n is 1 or 2 (mod 3).

A homeomorphism EXISTS as a topological space map via the finite
prefix-free code 3 -> 0, 6 -> 10, 9 -> 11; it cannot preserve the
specific measures. Neither product-space homeomorphism nor measure
theorem is claimed kernel checked in Agda or Lean.
"""
from fractions import Fraction
from math import gcd
import json


CODE = {'3': '0', '6': '10', '9': '11'}


def measure_binary_clopen_at_depth(n, chosen_prefixes):
    """Exact equal-depth disjoint cylinder union; returns a dyadic rational."""
    assert n >= 0
    assert len(chosen_prefixes) == len(set(chosen_prefixes))
    assert all(len(w) == n and set(w) <= {'0','1'} for w in chosen_prefixes)
    return Fraction(len(chosen_prefixes), 2**n)


def audit():
    # An explicit finite union cannot have ternary cylinder measure 1/3.
    for n in range(13):
        for k in range(2**n + 1):
            assert Fraction(k, 2**n) != Fraction(1, 3)
        # General all-depth proof: gcd(3,2^n)=1 and 3 does not divide 2^n.
        assert gcd(3, 2**n) == 1
        assert (2**n)%3 == (1 if n%2==0 else 2)
    assert sum(Fraction(1, 2**len(w)) for w in CODE.values()) == 1
    assert (Fraction(1,2),Fraction(1,4),Fraction(1,4)) != (
        Fraction(1,3),Fraction(1,3),Fraction(1,3))
    assert measure_binary_clopen_at_depth(2, ('00','01')) == Fraction(1,2)
    return {'clopen_measure_set_binary':'dyadic rational k/2^n',
            'uniform_ternary_first_digit_clopen_mass':'1/3',
            'measure_preserving_homeomorphism_possible':False,
            'topological_homeomorphism_possible':True,
            'obstruction':'3k = 2^n impossible mod 3 for any natural k,n',
            'finite_depth_regression_max':12,
            'kernel_verified':False}


if __name__ == '__main__':
    print(json.dumps(audit(), indent=2,sort_keys=True))
