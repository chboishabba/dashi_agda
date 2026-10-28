"""Action-sensitive 27 ternary words: orbit, Heaps and nonpromotion tests."""
from fractions import Fraction as F
from itertools import product,permutations
from pathlib import Path
import sys
import pytest

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/"scripts"))
from zipf_ternary27_action_heaps_exact import (
    TRITS,CUBE,S3,C3,axis_permute,relabel_values,conjugate_endomorphism,
    heaps_curve,orbit_partition,burnside_fixed_point_counts,
    exact_action_audit,uniform27_heaps_law,conditioned_six_order_law,
    information_loss_and_nonpromotion,
)


def test_all_27_words_and_four_exact_heaps_fibres():
    assert len(CUBE)==27 and len(set(CUBE))==27
    from collections import Counter
    actual=Counter(heaps_curve(w) for w in CUBE)
    assert actual=={
        (0,1,1,1):3,(0,1,1,2):6,
        (0,1,2,2):12,(0,1,2,3):6}
    assert uniform27_heaps_law()=={k:F(v,27) for k,v in actual.items()}


def test_burnside_all_four_distinct_actions_and_source_seven_shapes():
    audit=exact_action_audit()
    assert {k:v["orbit_count"] for k,v in audit.items()}=={
        "coordinate_S3":10,"coordinate_C3":11,
        "value_S3":5,"endomorphism_conjugacy_S3":7}
    assert sorted(audit["coordinate_S3"]["fixed_points"])==[3,3,9,9,9,27]
    assert sorted(audit["value_S3"]["fixed_points"])==[0,0,1,1,1,27]
    assert audit["endomorphism_conjugacy_S3"]["orbit_size_multiplicity"]=={
        1:1,2:1,3:2,6:3}
    assert audit["value_S3"]["heaps_invariant"]
    for action in ("coordinate_S3","coordinate_C3","endomorphism_conjugacy_S3"):
        assert not audit[action]["heaps_invariant"]


def test_conditioning_on_all_distinct_recovers_original_six_orders_not_c6():
    result=conditioned_six_order_law()
    assert result["evidence_probability"]==F(2,9)
    assert result["conditional"]=={
        word:F(1,6) for word in ("ABC","ACB","BAC","BCA","CAB","CBA")}
    # Uniform multiset permutation is the CONDITIONAL law, not IID
    # unconditional on three draws.
    assert sum(result["conditional"].values(),F())==1


def test_value_relabelling_preserves_entire_heaps_curve_for_162_cases():
    assert sum(heaps_curve(relabel_values(w,p))==heaps_curve(w)
               for w in CUBE for p in S3)==162


def test_position_permutations_do_not_preserve_full_discovery_curve():
    before=(-1,-1,0)
    after=axis_permute(before,(0,2,1))
    assert after==(-1,0,-1)
    assert heaps_curve(before)==(0,1,1,2)
    assert heaps_curve(after)==(0,1,2,2)
    assert set(before)==set(after)
    # Terminal number of distinct types is coordinate-symmetry invariant.
    for p in S3:
        for word in CUBE:
            assert heaps_curve(axis_permute(word,p))[-1]==heaps_curve(word)[-1]


def test_conjugation_is_not_just_value_or_coordinate_action():
    # An endomorphism table f has indexed INPUTS. Conjugation acts on
    # both domain and codomain; coordinate and value reorientation do not.
    assert len(orbit_partition(S3,conjugate_endomorphism))==7
    assert len(orbit_partition(S3,relabel_values))==5
    assert len(orbit_partition(S3,axis_permute))==10
    assert all(conjugate_endomorphism(w,(0,1,2))==w for w in CUBE)


def test_ternary_depths_and_spin_fingerprints_are_separate_types():
    audit=information_loss_and_nonpromotion()
    assert audit["ternary_cube"]==27
    assert audit["double_cube"]==729
    assert audit["distinct_ternary_depth5"]==243
    assert audit["distinct_five_mode_depth3"]==125
    assert audit["distinct_heaps_curves"]==4
    # Neither a 720-degree spin lift nor six root permutations follows
    # from integer cardinality 27, 243, 125 or 729.


def test_invalid_trits_and_illegal_group_actions_rejected():
    for bad in ((-1,0,2),(1,1),(False,0,1),(0,0,0,0)):
        with pytest.raises(ValueError):heaps_curve(bad)
    with pytest.raises(ValueError):axis_permute((0,1,-1),(0,0,1))
    with pytest.raises(ValueError):relabel_values((0,1,-1),(0,1,1))
    with pytest.raises(ValueError):conjugate_endomorphism((0,1,-1),(0,1,1))


def test_agda_owner_reuse_explicit_and_no_quaternion_same_object():
    src=(ROOT/"DASHI/Statistics/ZipfTernary27ActionHeapsExact.agda").read_text()
    umbrella=(ROOT/"DASHI/Statistics/ZipfFamilyEverything.agda").read_text()
    for symbol in (
        "Base369Ternary27HypervoxelFabricGeometryExact",
        "DASHI.Cognition.RecursiveFibreTower",
        "DASHI.Foundations.TernaryEndomorphismConjugacyExact",
        "DASHI.Statistics.ZipfFullHeapsCurveIdentityNoGoExact",
        "all27CodesHeapsInvariantUnderValueRelabeling",
        "coordinateSwapDoesNotPreserveAllHeaps",
        "existingConjugacyHasSevenOrbits",
        "cubeCodeRoundTrip","codeCubeRoundTrip"):
        assert symbol in src
    assert "ZipfTernary27ActionHeapsExact" in umbrella
    for flag in ("postulate\n","{!!}","NO_POSITIVITY_CHECK",
                 "allow-unsolved-metas","{-# TERMINATING #-}"):
        assert flag not in src
