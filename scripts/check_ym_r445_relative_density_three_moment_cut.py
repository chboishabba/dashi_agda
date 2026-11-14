#!/usr/bin/env python3
"""Exact arithmetic diagnostic for original R445 three-moment max-cut.

For two NORMALIZED measures on the same coarse configuration space,
the total-variation distance is a COMMON source-bound on the three
moment errors for F, G and FG whenever 0<=F,G<=1. If the unnormalised
effective-to-bare weight ratio s_i lies in [1-eps,1+eps], eps<1, then
TV <= eps (by the exact two-point extremal envelope).

THIS DOES NOT show that the original Wilson R445 effective and
bare couplings satisfy such a cutoff-uniform pointwise ratio bound.
No physical E1/D1 or Clay theorem is promoted. The source-native
coarse tests and original covariance telescope already exist in:
  YMClayE1D1OriginalR445BoundedMomentMajorantsExact.agda
  YMClayE1D1OriginalR445QuantitativeThreeMomentRGCutExact.agda
"""
from __future__ import annotations

import json
from fractions import Fraction


def normalized(weights: tuple[Fraction, ...]) -> tuple[Fraction, ...]:
    if not weights or any(w <= 0 for w in weights):
        raise ValueError("strictly positive finite weights required")
    total = sum(weights, Fraction(0))
    return tuple(w/total for w in weights)


def expectation(p: tuple[Fraction, ...], f: tuple[Fraction, ...]) -> Fraction:
    if len(p) != len(f):
        raise ValueError("dimension mismatch")
    return sum((x*y for x, y in zip(p, f)), Fraction(0))


def covariance(p: tuple[Fraction, ...], f: tuple[Fraction, ...],
               g: tuple[Fraction, ...]) -> Fraction:
    fg = tuple(x*y for x, y in zip(f, g))
    return expectation(p, fg)-expectation(p, f)*expectation(p, g)


def tv(p: tuple[Fraction, ...], q: tuple[Fraction, ...]) -> Fraction:
    if len(p) != len(q) or sum(p) != 1 or sum(q) != 1:
        raise ValueError("must be probability laws on the same carrier")
    return sum((abs(x-y) for x, y in zip(p, q)), Fraction(0))/2


def test_three_moments(
    effective_weights: tuple[Fraction, ...],
    bare_weights: tuple[Fraction, ...],
    f: tuple[Fraction, ...],
    g: tuple[Fraction, ...]) -> dict:
    p = normalized(effective_weights)
    q = normalized(bare_weights)
    if len(p) != len(q) or len(f) != len(p) or len(g) != len(p):
        raise ValueError("all source tests must be on the same coarse carrier")
    if any(not 0 <= z <= 1 for z in f + g):
        raise ValueError("only original unit-bounded test algebra admitted")
    fg = tuple(a*b for a, b in zip(f, g))
    d = tv(p, q)
    errors = {name: abs(expectation(p, h)-expectation(q, h))
              for name, h in (("F", f), ("G", g), ("FG", fg))}
    assert all(x <= d for x in errors.values())
    cov_error = abs(covariance(p, f, g)-covariance(q, f, g))
    assert cov_error <= sum(errors.values(), Fraction(0))
    assert cov_error <= 3*d
    return {
        "tv": str(d), "errors": {k: str(v) for k,v in errors.items()},
        "covariance_error": str(cov_error), "three_tv_bound": str(3*d)}


def relative_density_envelope(
    effective_weights: tuple[Fraction, ...],
    bare_weights: tuple[Fraction, ...]) -> dict:
    if len(effective_weights) != len(bare_weights):
        raise ValueError("same physical coarse carrier required")
    if any(w <= 0 for w in effective_weights+bare_weights):
        raise ValueError("all Wilson weights must be positive")
    ratios = [a/b for a,b in zip(effective_weights,bare_weights)]
    eps = max(abs(s-1) for s in ratios)
    p, q = normalized(effective_weights), normalized(bare_weights)
    d = tv(p,q)
    if eps < 1:
        assert d <= eps
    return {"pointwise_relative_error":str(eps),
            "normalized_TV":str(d), "deduced_TV_le_eps":eps<1}


def main() -> None:
    half = Fraction(1,2)
    tests = (
        ( (Fraction(3),Fraction(1)), (Fraction(1),Fraction(1)),
          (Fraction(1),Fraction(0)), (Fraction(1),Fraction(0)) ),
        ( (Fraction(6),Fraction(8),Fraction(2)),
          (Fraction(5),Fraction(7),Fraction(4)),
          (Fraction(1),half,Fraction(0)),
          (Fraction(0),Fraction(1),half) ),
        ( (Fraction(1),Fraction(1)), (Fraction(1),Fraction(1)),
          (Fraction(1),Fraction(0)), (Fraction(1),Fraction(0)) ),
    )
    receipts=[]
    for p,q,f,g in tests:
        receipts.append({
            "moments":test_three_moments(p,q,f,g),
            "ratio":relative_density_envelope(p,q)})
    # Fixed nonzero mismatch, no cutoff dependence. Merely having a
    # normalized RG pushforward does not identify the bare Gibbs law.
    assert receipts[0]["moments"]["covariance_error"]=="1/16"
    assert receipts[2]["moments"]["covariance_error"]=="0"
    print(json.dumps({
        "schema":"ym_r445_relative_density_three_moment_cut_v1",
        "exact_fraction_examples":receipts,
        "counterexample_fixed_effective_vs_bare_error": "1/16",
        "abstract_TV_to_three_moments_mathematical_lemma": True,
        "actual_Wilson_cutoff_uniform_relative_density_bound": False,
        "physical_R445_to_bare_E1D1_closed": False,
        "agda_kernel_accepted_here": False,
        "clay_mass_gap_closed": False
    },indent=2))


if __name__ == "__main__":
    main()
