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
        if name in ("miller", "yan"):
            assert "{-# OPTIONS --safe #-}" in content
        else:
            # Reused legacy source owners are not transitively --safe.
            assert "{-# OPTIONS --safe #-}" not in content
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
        "sameKernelResponseUnderOrderErasure",
        "prefixIgnoresFutureSuffix",
        "equalReceivedPrefixesGiveEqualOnlineStates",
        "equalReceivedPrefixesGiveEqualObservedOutputs",
        "arrivalCollisionWitness",
        "labelledArrivalCannotRecoverSourceOrder",
        "exactCalibrationRecoversOrderForTheseWorlds",
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
    assert "SpatialGradientBoundedUntilTime : PhysicalSource → Direction → Set" in text
    assert "SpatialGradientBoundedUntilTime selectedSource selectedDirection" in text
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
    cognition_rollup = (ROOT / "DASHI/Cognition/Everything.agda").read_text()
    assert "EnactedTemporalOrderExact" in cognition_rollup
    assert "EnactedTemporalOrderRegression" in cognition_rollup
    regression = (ROOT / "DASHI/Cognition/PNF/EnactedTemporalOrderRegression.agda").read_text()
    assert "sameCurrentStateForDifferentFuture" in regression
    assert "sameCurrentObservationForDifferentFuture" in regression
    assert "NSMillerAnisotropicA3BridgeExact" in (
        ROOT / "DASHI/Papers/NavierStokes/Everything.agda"
    ).read_text()
    assert "ThreePaperSourceAtlas20261025Exact" in (
        ROOT / "DASHI/Papers/Everything.agda"
    ).read_text()


def test_labelled_arrival_collision_requires_independent_delay_calibration():
    source = {
        "A": {"C_time": 0, "E_time": 50, "C_delay": 80, "E_delay": 10},
        "B": {"C_time": 50, "E_time": 0, "C_delay": 30, "E_delay": 60},
    }
    arrivals = {
        key: (
            data["C_time"] + data["C_delay"],
            data["E_time"] + data["E_delay"],
        )
        for key, data in source.items()
    }
    assert arrivals["A"] == arrivals["B"] == (80, 60)
    actual_source_order = {
        key: "C-before-E" if data["C_time"] < data["E_time"]
        else "E-before-C" for key, data in source.items()
    }
    assert actual_source_order["A"] != actual_source_order["B"]
    assert source["A"]["C_delay"] != source["B"]["C_delay"]
    assert source["A"]["E_delay"] != source["B"]["E_delay"]
    for key, data in source.items():
        recovered_c = arrivals[key][0] - data["C_delay"]
        recovered_e = arrivals[key][1] - data["E_delay"]
        assert (recovered_c, recovered_e) == (
            data["C_time"], data["E_time"]
        )
        assert (
            "C-before-E" if recovered_c < recovered_e else "E-before-C"
        ) == actual_source_order[key]
    text = (ROOT / FILES["temporal"]).read_text()
    assert "not an oracle revealing source event order" in text
    assert "labelledArrivalCannotRecoverSourceOrder" in text
    regression = (
        ROOT / "DASHI/Cognition/PNF/EnactedTemporalOrderRegression.agda"
    ).read_text()
    assert "sourceOrderWithFirstCalibration" in regression
    assert "sourceOrderWithSecondCalibration" in regression


def test_semantic_fidelity_reuses_generic_no_go_and_has_two_real_collisions():
    exact = (
        ROOT / "DASHI/Papers/ThreePaperConsumerFidelity20261026Exact.agda"
    ).read_text()
    regression = (
        ROOT / "DASHI/Papers/ThreePaperConsumerFidelity20261026Regression.agda"
    ).read_text()
    for theorem in (
        "pressureSourceLossWitness",
        "erasedForcingCannotRecoverSourcePressureCorrection",
        "sourceDomainLossWitness",
        "domainBlindEstimateCannotDetermineMillerSource",
    ):
        assert theorem in exact
    assert "DASHI.Core.IntersectionalNonFactorability" in exact
    assert "DASHI.Core.InterpretiveFormalisationCoreExact" in exact
    assert "DASHI.Foundations.ClaimScopeCertificateExact" in exact
    assert "arXiv:2610.08144" in exact
    assert "DASHI extension" in exact
    assert "forcingStatusIsLost" in regression
    assert "domainErasureCannotProduceMillerSource" in regression
    assert "ThreePaperConsumerFidelity20261026Exact" in (
        ROOT / "DASHI/Papers/Everything.agda"
    ).read_text()
    assert "ThreePaperConsumerFidelity20261026Regression" in (
        ROOT / "DASHI/Papers/Everything.agda"
    ).read_text()
    assert not re.search(r"(?m)^\s*postulate\b", exact)
    assert "{!!}" not in exact


def test_original_source_atlas_records_semantic_critique_as_contested():
    atlas = source("atlas")
    for phrase in (
        "semanticFidelityCritique2026",
        "Alexander Bastounis; Fabian Circelli; Anders C. Hansen",
        "2610.08144",
        "millerProjectionFirstImplementation",
        "semanticFidelityWitnessFirstImplementation",
        "Chronology.sourceCommittedOnly",
    ):
        assert phrase in atlas
    assert "does not challenge soundness of the Lean kernel" in atlas


def test_two_source_hypothesis_collisions_have_identical_flat_views():
    force_worlds = (
        ("divergenceFreeForcing", "pressureWithoutForceDivergence",
         "noForcingCorrection"),
        ("forcingWithNonzeroDivergence", "pressureWithoutForceDivergence",
         "nonzeroForcingCorrection"),
    )
    domain_worlds = (
        ("unforcedWholeSpaceR3", "navierStokesEstimateLabel", "physicalR3"),
        ("periodicGalerkinT3", "navierStokesEstimateLabel", "physicalT3"),
    )
    for pair in (force_worlds, domain_worlds):
        assert pair[0][1] == pair[1][1]
        assert pair[0][2] != pair[1][2]
