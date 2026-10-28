"""Actual anchor-normalization quotient transport, not a 41=41 number weld."""
import sys
from pathlib import Path
from itertools import product
import pytest
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/"scripts"))
from alexander_horned_s3_word_sign_orbit_transport_exact import (
    check,trits,rgs,relative,sign_orbit,transform,stirling_at_most_3
)

def test_all_word_orbit_classes_and_global_s3_actions():
    receipt=check()
    assert receipt["status"]=="PASS"
    assert receipt["named_words_checked"]==9840
    assert receipt["full_s3_transform_checks"]==59040
    assert [v["s3_pattern_classes"] for v in
            receipt["orbit_transport_by_depth"].values()]==[
        1,2,5,14,41,122,365,1094]

def test_genuine_three_word_five_orbit_bijection():
    rgs_to_sign={}
    sign_to_rgs={}
    for word in product(range(3),repeat=3):
        partition=rgs(word)
        quotient=sign_orbit(relative(word))
        assert rgs_to_sign.setdefault(partition,quotient)==quotient
        assert sign_to_rgs.setdefault(quotient,partition)==partition
    assert len(rgs_to_sign)==len(sign_to_rgs)==5
    # The values themselves are NOT identical: maps use anchor subtraction.
    assert rgs_to_sign[(0,1,0)]==sign_orbit((1,0))
    assert rgs_to_sign[(0,1,1)]==sign_orbit((1,1))

def test_stirling_identity_is_all_depth_not_five_only():
    assert [stirling_at_most_3(n+1) for n in range(8)]==[
        (3**n+1)//2 for n in range(8)]

def test_strict_domains_and_raw_object_identity_boundary():
    for invalid in (-1,8,True,2.5):
        with pytest.raises(ValueError):list(trits(invalid))
    for invalid in (0,9,True,1.5):
        with pytest.raises(ValueError):stirling_at_most_3(invalid)
    with pytest.raises(ValueError):relative(())
    with pytest.raises(ValueError):transform((0,1,2),3,1)
    with pytest.raises(ValueError):transform((0,1,2),1,0)

def test_reuses_existing_owner_in_actual_agda_transport():
    agda=(ROOT/"DASHI/Mathematics/Topology/"
          "AlexanderHornedS3WordSignOrbitTransportExact.agda").read_text()
    root=(ROOT/"DASHI/EverythingTOESymmetryResolved369.agda").read_text()
    for term in ("as Phase","tritPhaseRoundTrip","normaliseTranslate",
                 "normaliseReflection","signedRelativeTranslationInvariant",
                 "signedRelativeReflection","signedRelativeSection",
                 "normaliseViaTranslation",
                 "normaliseSameImpliesTranslate",
                 "signedOrbitToGlobalS3","globalS3ToSignedOrbit",
                 "signedOrbitIffGlobalAffineS3"):
        assert term in agda
    assert "import DASHI.Mathematics.Topology.AlexanderHornedS3WordSignOrbitTransportExact" in root
    for escape in ("postulate\n","{!!}","allow-unsolved-metas",
                   "NO_POSITIVITY_CHECK","{-# TERMINATING #-}"):
        assert escape not in agda
