"""Adversarial finite verification of reused SSSP ABC/six Heaps adapter."""
from collections import Counter
from fractions import Fraction as F
from itertools import permutations, product
from pathlib import Path
import sys
import pytest

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
from zipf_abc_six_order_receipt import (
    ABC_ORDERS, all_distinct_orders, min_tail_encode, min_tail_decode,
    relation_sheet, three_unique_order_receipt,
    repeated_a_three_type_receipt, uniform_multiset_curves,
)
from zipf_heaps_bridge import (
    observed_prefix_diversity, novelty_flags, distinct_envelope,
    multiset_heaps_extremal_profiles, multiset_heaps_area_gap,
)


def test_exact_six_order_source_carrier_and_all_three_letter_permutations():
    independent={"".join(word) for word in permutations("ABC")}
    assert len(independent)==6
    assert all_distinct_orders()==ABC_ORDERS==tuple(sorted(independent))
    assert all(observed_prefix_diversity(word)==(0,1,2,3)
               for word in independent)
    assert all(novelty_flags(word)==(True,True,True) for word in independent)


def test_minimum_and_tail_codec_roundtrip_exact_three_times_two():
    codes=[min_tail_encode(word) for word in ABC_ORDERS]
    assert len(set(codes))==6
    assert set(codes)==set(product("ABC",(0,1)))
    assert all(min_tail_decode(code)==word
               for word,code in zip(ABC_ORDERS,codes))
    assert all(min_tail_encode(min_tail_decode(code))==code for code in codes)


def test_full_pair_relation_sheet_keeps_six_separate():
    sheets={word:relation_sheet(word) for word in ABC_ORDERS}
    assert len(set(sheets.values()))==6
    for sheet in sheets.values():
        assert len(sheet)==9
        assert all(sheet[3*i+i]==0 for i in range(3))
        assert all(sheet[3*i+j]==-sheet[3*j+i]
                   for i in range(3) for j in range(3))
    assert sheets["ABC"]!=sheets["ACB"]


def test_six_to_one_vs_six_to_three_observation_quotients():
    receipt=three_unique_order_receipt()
    assert receipt["curve"]==(0,1,2,3)
    assert receipt["full_curves_distinct"]==1
    assert receipt["relation_sheets_distinct"]==6
    assert receipt["min_tail_codes_distinct"]==6
    assert receipt["minimum_counts"]=={"A":2,"B":2,"C":2}
    assert receipt["minimum_probabilities"]==dict.fromkeys("ABC",F(1,3))
    # 1 singleton Heaps curve with probability 1; each whole order 1/6.
    assert sum(receipt["minimum_probabilities"].values())==1


def test_s3_is_not_a_cyclic_six_group_from_cardinality_alone():
    # Under standard composition, swap AB and swap BC do not commute.
    swap_ab={"A":"B","B":"A","C":"C"}
    swap_bc={"A":"A","B":"C","C":"B"}
    compose=lambda x,y:{z:x[y[z]] for z in "ABC"}
    assert compose(swap_ab,swap_bc)!=compose(swap_bc,swap_ab)


def test_repeated_a_twelve_orders_exact_curve_fibre_counts():
    receipt=repeated_a_three_type_receipt()
    dist=receipt["curve_probabilities"]
    assert receipt["total_distinct_orders"]==12
    assert dist=={
        (0,1,1,2,3):F(2,12),
        (0,1,2,2,3):F(4,12),
        (0,1,2,3,3):F(6,12),
    }
    assert receipt["lower"]==(0,1,1,2,3)
    assert receipt["upper"]==(0,1,2,3,3)
    assert receipt["heaps_area_gap"]==2


def test_without_replacement_expected_profile_independent_enumeration():
    words=set(permutations("AABC"))
    assert len(words)==12
    curves=Counter(observed_prefix_diversity(word) for word in words)
    independent={curve:F(f,12) for curve,f in curves.items()}
    assert independent==uniform_multiset_curves((2,1,1))
    assert [sum(F(curve[t])*mass for curve,mass in independent.items())
            for t in range(5)]==[F(0),F(1),F(11,6),F(5,2),F(3)]


def test_sharp_heaps_envelope_matches_each_repeated_case():
    for counts in ((1,1,1),(2,1,1),(2,2,1),(3,1,1)):
        d=uniform_multiset_curves(counts)
        lower,upper=multiset_heaps_extremal_profiles(counts)
        assert lower in d and upper in d
        for curve in d:
            assert all(distinct_envelope(counts,t)[0] <= curve[t] <=
                       distinct_envelope(counts,t)[1]
                       for t in range(sum(counts)+1))
        assert multiset_heaps_area_gap(counts)==sum(
            u-l for l,u in zip(lower,upper))


def test_invalid_inputs_fail_closed():
    for value in ("AAB","ABCD","",None):
        with pytest.raises(ValueError):min_tail_encode(value)
    for code in (("D",0),("A",2),("A",True),("A",0,1),None):
        with pytest.raises(ValueError):min_tail_decode(code)
    with pytest.raises(ValueError):uniform_multiset_curves((2,0,1))
    with pytest.raises(ValueError):uniform_multiset_curves((True,1,1))
    with pytest.raises(ValueError):uniform_multiset_curves((8,1,1))


def test_original_agda_owners_are_imported_not_redefined():
    src=(ROOT/"DASHI/Statistics/ZipfABC6OrderHeapsQuotientExact.agda").read_text()
    root=(ROOT/"DASHI/Statistics/ZipfFamilyEverything.agda").read_text()
    assert "import DASHI.Computation.SSSPThreeFrontierLinearExtensionQuotientBidiExact" in src
    assert "import DASHI.Computation.SSSPThreeFrontierMinimumOrbitQuotientExact" in src
    assert "import DASHI.Computation.SSSPThreeFrontierBinaryTernaryFactorExact" in src
    assert "allSixFullHeapsCurvesCoincide" in src
    assert "allSixTerminalHistogramsCoincide" in src
    assert "noFirstLabelRecoveryFromFullHeapsCurve" in src
    assert "noTailRecoveryFromFullHeapsCurve" in src
    assert "Code.orderRoundTrip" in src
    assert "import DASHI.Statistics.ZipfABC6OrderHeapsQuotientExact" in root
    for forbidden in ("{-# TERMINATING #-}", "postulate\n", "{!!}",
                      "NO_POSITIVITY_CHECK", "allow-unsolved-metas"):
        assert forbidden not in src
