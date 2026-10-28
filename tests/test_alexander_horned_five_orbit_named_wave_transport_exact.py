"""Finite 3-label word-S3 → native five-orbit wave operator bridge."""
from pathlib import Path
import sys
import pytest

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/"scripts"))
from alexander_horned_five_orbit_named_wave_transport_exact import (
    check,orbit_of_word, PATTERN_TO_SLOT, SLOTS
)

def test_all_243_five_phase_fields_and_six_s3_word_actions():
    r=check()
    assert r["status"]=="PASS"
    assert r["affine_s3_operator_checks"]==39366
    assert r["five_orbit_fields"]==243
    assert r["named_word_patterns"]==5

def test_actual_five_named_equality_slots():
    assert PATTERN_TO_SLOT=={
        (0,0,0):"origin",(0,0,1):"axisSecond",
        (0,1,0):"axisFirst",(0,1,1):"diagonal",
        (0,1,2):"antiDiagonal"}
    assert len(SLOTS)==5
    for bad in ((),(0,1),(0,1,2,0),(-1,0,1),(0,1,True)):
        with pytest.raises(ValueError):orbit_of_word(bad)

def test_imports_existing_five_orbit_operator_and_word_transport_owners():
    src=(ROOT/"DASHI/Mathematics/Topology/"
        "AlexanderHornedFiveOrbitNamedWordWaveTransportExact.agda").read_text()
    umbrella=(ROOT/"DASHI/EverythingTOESymmetryResolved369.agda").read_text()
    for inherited in ("AlexanderHornedDepthTwoFiveOrbitFibreExact",
                      "AlexanderHornedFiveOrbitWaveOperatorExact",
                      "AlexanderHornedS3WordSignOrbitTransportExact"):
        assert inherited in src
    for proof in ("wordOrbitTranslationInvariant","wordOrbitReflectionInvariant",
                  "aaaOrbit","aabOrbit","abaOrbit","abbOrbit","abcOrbit",
                  "namedEvolutionFactor","namedEvolutionTranslationInvariant",
                  "namedEvolutionReflectionInvariant"):
        assert proof in src
    assert "import DASHI.Mathematics.Topology.AlexanderHornedFiveOrbitNamedWordWaveTransportExact" in umbrella
    for forbidden in ("postulate\n","{!!}","allow-unsolved-metas",
                      "NO_POSITIVITY_CHECK","{-# TERMINATING #-}"):
        assert forbidden not in src
