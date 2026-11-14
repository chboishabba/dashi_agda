"""Independent arithmetic and source-surface checks for F13b.

Exact rational checks support, but DO NOT kernel-verify, the Agda proof.
Classical arithmetic / Agda stdlib original authors retain mathematical
ownership. Johl Brown-directed OpenAI ChatGPT regression, 2026-10-28.
"""
from fractions import Fraction
from itertools import product
from math import gcd
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]


def test_exact_cross_addition_and_canonical_gcd_4096_pairs():
    items=list(product(range(8),range(1,9)))
    checked=0
    for n,d in items:
        for m,e in items:
            raw_n,raw_d=n*e+m*d,d*e
            rational=Fraction(n,d)+Fraction(m,e)
            assert raw_d>0
            assert Fraction(raw_n,raw_d)==rational
            g=gcd(raw_n,raw_d)
            assert (raw_n//g,raw_d//g)==(
                rational.numerator,rational.denominator)
            checked+=1
    assert checked==4096


def test_finite_hurwitz_fold_identity_all_shift_shape_and_empty_cases():
    checked=0
    for count,shift,exponent in product(range(14),range(7),range(8)):
        numerator,denominator=0,1
        for r in range(count):
            d=(r+shift+1)**exponent
            numerator,denominator=numerator*d+denominator,denominator*d
        expected=sum((Fraction(1,(r+shift+1)**exponent)
                      for r in range(count)),Fraction())
        assert denominator>0 and Fraction(numerator,denominator)==expected
        checked+=1
    assert checked==784


def test_zero_denominator_is_not_valid_rational_domain():
    for numerator in range(12):
        try:
            Fraction(numerator,0)
        except ZeroDivisionError:
            pass
        else:
            raise AssertionError("zero denominator accepted")


def test_f13b_bridges_real_standard_library_owners_not_synthetic_assumptions():
    bridge=(ROOT/"DASHI/Statistics/ZipfFractionAddRationalBridgeExact.agda").read_text()
    fold=(ROOT/"DASHI/Statistics/ZipfFractionFoldConditionalExact.agda").read_text()
    entry=(ROOT/"DASHI/Statistics/ZipfFamilyEverything.agda").read_text()
    for symbol in ("Data.Rational.Unnormalised.Base",
                   "Data.Rational.Unnormalised.Properties",
                   "fromℚᵘ-cong","fromℚᵘ-toℚᵘ","toℚᵘ-fromℚᵘ",
                   "toℚᵘ-homo-+","rawFractionAddPreserved",
                   "positiveDenominatorAddHomomorphism"):
        assert symbol in bridge
    assert "Nat.NonZero (Fraction.denominator a)" in bridge
    assert "AddBridge.positiveDenominatorAddHomomorphism" in fold
    assert "concreteHurwitzSourceWritten" in fold
    assert "ZipfFractionAddRationalBridgeExact" in entry
    for agda in (bridge,fold):
        for forbidden in ("{-# TERMINATING #-}", "NO_POSITIVITY_CHECK",
                          "allow-unsolved-metas", "{!!}", "postulate\n"):
            assert forbidden not in agda


def test_existing_finite_zipf_source_does_not_use_unchecked_quotient():
    source=(ROOT/"DASHI/Statistics/ZipfFamilyFiniteExact.agda").read_text()
    assert "sumFirstDenominatorNonZero" in source
    assert "finiteHurwitzDenominatorNonZero" in source
    assert "mandelbrotDenominatorNonZero" in source
    assert "postulate\n" not in source
