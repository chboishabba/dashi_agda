"""Exact finite negative controls for F13b guarded fold and H15 identity loss.

Numerical checks are not Agda kernel proofs. The *mathematical* content is
classical fraction addition and finite token information loss.
Johl Brown + OpenAI ChatGPT repository regression, 2026-10-28.
"""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import sys
import pytest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
from zipf_f13_pnf_parity_exact import (
    source_unreduced_hurwitz_fraction, constructive_pnf_masses
)
from zipf_heaps_bridge import observed_prefix_diversity, novelty_flags


def _positive_fraction(num, den):
    if type(num) is not int or type(den) is not int or den <= 0:
        raise ValueError('source fraction interpretation requires positive denominator')
    return F(num, den)


def _unreduced_add(a, b):
    na, da = a
    nb, db = b
    if da <= 0 or db <= 0:
        raise ValueError('addition only admitted on positive denominators')
    return (na * db + nb * da, da * db)


def test_general_signed_fraction_addition_homomorphism_finite_grid():
    for na, nb, da, db in product(range(-3, 4), range(-3, 4), range(1, 5), range(1, 5)):
        a, b = (na, da), (nb, db)
        n, d = _unreduced_add(a, b)
        assert _positive_fraction(n, d) == (
            _positive_fraction(*a) + _positive_fraction(*b))


def test_zero_denominator_is_never_interpreted():
    for bad in ((0,0), (1,0),(-1,0),(1,-3)):
        with pytest.raises(ValueError):
            _positive_fraction(*bad)
    with pytest.raises(ValueError):
        _unreduced_add((1,2), (5,0))


def test_generic_fold_preserves_rational_interpretation():
    for length in range(1,7):
        for nums in product((0,1,2),repeat=length):
            terms = [(num,(i%3)+1) for i,num in enumerate(nums)]
            folded = (0,1)
            for x in terms:
                folded = _unreduced_add(folded,x)
            assert _positive_fraction(*folded) == sum(
                (_positive_fraction(*x) for x in terms),F())


def test_source_zipf_fold_matches_existing_pnf_mass_map():
    for k,s,q in product(range(1,11),range(6),range(4)):
        n,d = source_unreduced_hurwitz_fraction(k,s,q)
        weights = tuple(F(1,(r+q)**s) for r in range(k,0,-1))
        assert F(n,d) == sum(weights,F())
        assert constructive_pnf_masses(k,s,q) == tuple(
            w/F(n,d) for w in weights)


def test_same_entire_curve_histogram_but_distinct_repeated_identity():
    left = (0,1,0,2,1)
    right = (0,1,1,2,0)
    assert left != right
    assert tuple(left.count(i) for i in range(3)) == (2,2,1)
    assert tuple(right.count(i) for i in range(3)) == (2,2,1)
    assert observed_prefix_diversity(left) == observed_prefix_diversity(right) == (
        0,1,2,2,3,3)
    assert novelty_flags(left) == novelty_flags(right) == (True,True,False,True,False)
    assert left[2] != right[2]


def test_every_short_word_curve_differences_recover_novelty_flags():
    for k in range(1,4):
        for n in range(7):
            for word in product(range(k),repeat=n):
                curve = observed_prefix_diversity(word)
                flags = novelty_flags(word)
                assert len(curve) == n+1
                assert tuple(v-u == 1 for u,v in zip(curve,curve[1:])) == flags


def test_guarded_agda_source_has_no_unsafe_axiom_or_false_promotion():
    guarded = (ROOT/'DASHI/Statistics/ZipfFractionFoldConditionalExact.agda').read_text()
    h15 = (ROOT/'DASHI/Statistics/ZipfFullHeapsCurveIdentityNoGoExact.agda').read_text()
    f13 = (ROOT/'DASHI/Statistics/ZipfPNFConstructiveNormalizationExact.agda').read_text()
    umbrella = (ROOT/'DASHI/Statistics/ZipfFamilyEverything.agda').read_text()
    for content in (guarded,h15,f13):
        for banned in ('postulate\n', '{!!}', 'TERMINATING\n',
                       'NO_POSITIVITY_CHECK', 'allow-unsolved-metas'):
            assert banned not in content
    assert 'Nat.NonZero (Fraction.denominator a)' in guarded
    assert 'addition-preserved' in guarded and 'sourceHurwitzEqualsRationalFold' in guarded
    assert 'ConcreteAddLaw : Set' in guarded
    assert 'concreteRankTermPreserved' in guarded
    assert 'concreteSourceHurwitzEqualsRationalFold' in guarded
    assert 'fullCurveCannotRecoverRepeatedIdentity' in h15
    assert 'finiteZipfWeightIdentificationPaid' not in f13 or 'false' in f13
    for name in ('ZipfFractionFoldConditionalExact',
                 'ZipfFullHeapsCurveIdentityNoGoExact'):
        assert 'import DASHI.Statistics.'+name in umbrella
