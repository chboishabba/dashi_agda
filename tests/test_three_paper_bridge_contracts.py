"""Static source/proof-boundary regression for three user-supplied papers.

The static contract is not an Agda typecheck. Finite algebra and order tests
below use Python's own semantics and do not certify the attached physical model.
"""
from pathlib import Path
import itertools
import re

ROOT = Path(__file__).resolve().parents[1]
FILES = {
    "temporal": "DASHI/Cognition/PNF/EnactedTemporalOrderExact.agda",
    "miller": "DASHI/Physics/Closure/NSMillerAnisotropicA3BridgeExact.agda",
    "yan": "DASHI/Physics/Closure/NSYanRadulescuStationaryPressureExact.agda",
    "atlas": "DASHI/Papers/ThreePaperSourceAtlas20261025Exact.agda",
}


def source(name: str) -> str:
    return (ROOT / FILES[name]).read_text(encoding="utf-8")


def test_no_postulates_metavariables_or_unearned_promotions():
    for name in FILES:
        content = source(name)
        assert "{-# OPTIONS --safe #-}" in content
        assert not re.search(r"(?m)^\s*postulate\b", content)
        assert "{!!}" not in content
        assert "clayPromotion = true" not in content


def test_finite_order_proof_reuses_original_generic_owner():
    text = source("temporal")
    assert "DASHI.Core.IntersectionalNonFactorability" in text
    for term in [
        "orderErasureWitness",
        "featureBagCannotRecoverDirectedOrder",
        "relabelledBagCannotRecoverOrder",
        "prefixSuffixLaw",
        "receptionEC",
        "calibratedReadoutIfEstimatesCorrect",
        "laterRetrievalDoesNotChangeAdmission",
        "absentUptakeFailsStipulatedAdmission",
    ]:
        assert term in text
    pairs = list(itertools.permutations(["C", "E", "G"], 2))
    unordered = {frozenset(pair) for pair in pairs}
    assert len(pairs) == 6
    assert len(unordered) == 3
    assert {frozenset(("C", "E")): ("C", "E")} != {
        frozenset(("C", "E")): ("E", "C")
    }


def test_miller_requires_published_rule_and_same_source_a3_transfer():
    text = source("miller")
    assert "NSCanonicalA3ContinuationResidualExact" in text
    assert "MillerPhysicalPremises" in text
    assert "CriticalProjectedVorticityFinite" in text
    assert "SpatialGradientBoundedUntilTime" in text
    assert "SameSolutionDirection" in text
    assert "publishedMillerImplication" in text
    assert "sameSourceA3Transfer" in text
    assert "continuationCriterionLiteralNS" in text


def test_yan_keeps_force_divergence_and_requires_zero_to_suppress():
    text = source("yan")
    assert "exactForcedPressureEquation" in text
    assert "pressureLaplacian ≡ (forceDivergence - convectiveContraction)" in text
    assert "divf ≡ zero" in text
    for force_div, conv_div in [(3.0, 1.5), (0.0, -2), (-4.0, 0.25)]:
        pressure_lap = force_div - conv_div
        assert abs(pressure_lap + conv_div - force_div) < 1e-10
        if force_div:
            assert pressure_lap != -conv_div


def test_atlas_uses_exact_original_roots_and_no_citation_promotion():
    text = source("atlas")
    for doi in [
        "10.1090/bproc/74",
        "10.1007/s12215-020-00540-3",
        "10.5281/zenodo.23591626",
    ]:
        assert doi in text
    assert "AttributedSourceCore" in text
    assert "SnowballAttributionProvenanceInvariantExact" in text
    assert "chaeChoe1999" in text
    assert "openaiForced2026" in text
    assert "smooth-FORCED" in text
    assert "unforced A/B" in text


def test_domain_rollups_are_linked_without_new_round_owners():
    assert "EnactedTemporalOrderExact" in (
        ROOT / "DASHI/Cognition/Everything.agda"
    ).read_text()
    assert "NSMillerAnisotropicA3BridgeExact" in (
        ROOT / "DASHI/Papers/NavierStokes/Everything.agda"
    ).read_text()
    assert "ThreePaperSourceAtlas20261025Exact" in (
        ROOT / "DASHI/Papers/Everything.agda"
    ).read_text()
