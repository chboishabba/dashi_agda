"""F13b own original source->PNF identity: exact arithmetic and proof gates.

Checks use Python's normalized Fraction as an INDEPENDENT arithmetic oracle
and do not assert a compiled Agda kernel receipt. The original finite raw
Fraction, normalized ℚ and PNF atom owners remain unchanged.
"""
from fractions import Fraction
from itertools import product
from pathlib import Path
from math import gcd

ROOT=Path(__file__).resolve().parents[1]


def source_fraction_sum(count, shift, exponent):
    """Exact analogue of ORIGINAL finiteHurwitz/sumFirst/addFraction."""
    num,den=0,1
    for r in range(count):
        d=(r+shift+1)**exponent
        num,den=num*d+den,den*d
    return num,den


def original_pnf_mass_list(count,shift,exponent):
    """Existing source construction: per-rank reciprocal divided by rawSum."""
    assert count>0
    terms=[Fraction(1,(r+shift+1)**exponent) for r in range(count)]
    z=sum(terms,Fraction())
    assert z>0
    return [t/z for t in terms],z


def test_source_fraction_normalization_matches_original_pnf_total():
    checked=0
    for count,shift,exponent in product(range(1,15),range(7),range(7)):
        raw_n,raw_d=source_fraction_sum(count,shift,exponent)
        atoms,z=original_pnf_mass_list(count,shift,exponent)
        assert raw_n>=0 and raw_d>0
        assert Fraction(raw_n,raw_d)==z
        assert Fraction(raw_n,raw_d)*Fraction(1,1)/z==sum(atoms,Fraction())==1
        checked+=1
    assert checked==14*7*7


def test_zero_count_raw_fraction_and_positive_support_gate():
    for shift,exponent in product(range(6),range(6)):
        n,d=source_fraction_sum(0,shift,exponent)
        assert (n,d)==(0,1)
        assert Fraction(n,d)==0
    # F13b's scaled-to-one theorem requires suc n: no inverse Z(0).
    assert sum((),Fraction())==0


def test_source_fraction_addition_and_normalization_are_valid_only_with_positive_d():
    count=0
    for a,b,c,d in product(range(6),range(1,7),range(6),range(1,7)):
        n=a*d+c*b
        den=b*d
        got=Fraction(n,den)
        assert got==Fraction(a,b)+Fraction(c,d)
        gg=gcd(n,den)
        assert (n//gg,den//gg)==(got.numerator,got.denominator)
        count+=1
    assert count==6*6*6*6


def test_f13b_canonical_source_owner_chain_is_real_and_never_paid_without_kernel():
    src=(ROOT/"DASHI/Statistics/ZipfF13bSourcePNFIntegrationExact.agda").read_text()
    fold=(ROOT/"DASHI/Statistics/ZipfFractionFoldConditionalExact.agda").read_text()
    pnf=(ROOT/"DASHI/Statistics/ZipfPNFConstructiveNormalizationExact.agda").read_text()
    fraction=(ROOT/"DASHI/Statistics/ZipfFamilyFiniteExact.agda").read_text()
    umbrella=(ROOT/"DASHI/Statistics/ZipfFamilyEverything.agda").read_text()
    for theorem in ("sourceFiniteHurwitz", "sourceFiniteHurwitzEqualsRawSum",
                    "sourceScaledTotalEqualsPNFTotal",
                    "sourceFiniteHurwitzScaledToOne"):
        assert theorem in src
    for owner in ("ZipfFractionFoldConditionalExact","ZipfPNFConstructiveNormalizationExact",
                  "ZipfFamilyFiniteExact","GenericExpectedFibreRateExact"):
        assert owner in src
    assert "Fold.concreteHurwitzSourceWritten" in src
    assert "PNF.scaledSumFactors" in src
    assert "PNF.atomsTotalEqualsScaledSum" in src
    assert "PNF.zipfPNFAtomsNormalize" in src
    assert "finiteHurwitzDenominatorNonZero" in fraction
    assert "concreteAddLawSourceWritten" in fold
    assert "finiteZipfPNFAdapter" in pnf
    assert "\n    false\n" in pnf
    assert "import DASHI.Statistics.ZipfF13bSourcePNFIntegrationExact" in umbrella
    for forbidden in ("postulate\n","{!!}","allow-unsolved-metas",
                      "NO_POSITIVITY_CHECK","{-# TERMINATING #-}"):
        assert forbidden not in src
