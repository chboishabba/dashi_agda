from __future__ import annotations

import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def _read(path: str) -> str:
    return (ROOT / path).read_text(encoding="utf-8")


def _import_lines(text: str) -> str:
    return "\n".join(
        line for line in text.splitlines()
        if line.lstrip().startswith(("import ", "open import "))
    )


def _assert_safe_surface(text: str) -> None:
    assert "{-# OPTIONS --safe #-}" in text
    assert "{!!}" not in text
    assert "--allow-unsolved-metas" not in text
    assert not re.search(r"(?m)^\s*postulate\b", text)


def _assert_round_free_safe_owner(path: str) -> str:
    text = _read(path)
    _assert_safe_surface(text)
    assert "Round" not in _import_lines(text)
    return text


def test_ns_canonical_root_is_concrete_nonround_run_target():
    data = json.loads(_read(".dashi/canonical-roots.json"))
    roots = data["roots"]
    assert "DASHI.Physics.Closure.NSConcreteLiteralClayABCDRunTargetExact" in roots
    assert "DASHI.Physics.Closure.NSLiteralClayABCDCapstone" not in roots
    assert "DASHI.Physics.Closure.NSClayOfficialSemanticPromotionBoundaryExact" not in roots
    assert data["policy"]["rounds_authoritative_by_default"] is False
    assert data["policy"]["body_only_equivalence_is_semantic_evidence"] is False


def test_literal_abcd_uses_nonround_forced_breakdown_coordinates():
    text = _read("DASHI/Physics/Closure/NSClayLiteralABCDExact.agda")
    imports = _import_lines(text)
    assert "NSClayForcedBreakdownSourceCoordinatesExact" in imports
    assert "NSTriadKNClayForcedBreakdownFormulationRound523Exact" not in imports


def test_forced_breakdown_coordinate_owner_is_safe_and_round_free():
    text = _read(
        "DASHI/Physics/Closure/NSClayForcedBreakdownSourceCoordinatesExact.agda"
    )
    _assert_safe_surface(text)
    assert "Round" not in _import_lines(text)
    for name in [
        "positiveViscosity",
        "rapidInitialSpatialDecay",
        "periodicInitialDatum",
        "rapidForcingSpaceTimeDecay",
        "rapidForcingTimeDecay",
        "boundedEnergyRequirement",
        "periodicSolutionRequirement",
        "requiredByC",
        "requiredByD",
    ]:
        assert name in text


def test_literal_abcd_preserves_forced_coordinate_checks():
    text = _read("DASHI/Physics/Closure/NSClayLiteralABCDExact.agda")
    for name in [
        "cRequiresPositiveViscosity",
        "cRequiresRapidInitialSpatialDecay",
        "cRequiresRapidForcingSpaceTimeDecay",
        "cRequiresBoundedEnergy",
        "dRequiresPositiveViscosity",
        "dRequiresPeriodicInitialDatum",
        "dRequiresRapidForcingTimeDecay",
        "dRequiresPeriodicSolution",
    ]:
        assert name in text


CANONICAL_RESIDUAL_OWNERS = [
    "DASHI/Physics/Closure/NSCanonicalA1PhysicalPopulationResidualExact.agda",
    "DASHI/Physics/Closure/NSCanonicalA2MajorantResidualExact.agda",
    "DASHI/Physics/Closure/NSCanonicalA3ContinuationResidualExact.agda",
    "DASHI/Physics/Closure/NSCanonicalB4PhysicalR440PaymentResidualExact.agda",
    "DASHI/Physics/Closure/NSCanonicalB123PhysicalProducerResidualExact.agda",
    "DASHI/Physics/Closure/NSCanonicalB7IntegratedControlResidualExact.agda",
    "DASHI/Physics/Closure/NSCanonicalBContinuationResidualExact.agda",
    "DASHI/Physics/Closure/NSCanonicalCDReleasedReconstructionResidualExact.agda",
]


def test_ns_evidence_backed_residual_owners_are_safe_and_round_free():
    for path in CANONICAL_RESIDUAL_OWNERS:
        text = _assert_round_free_safe_owner(path)
        assert "DASHI extension" in text
        assert "clayPromotion = true" not in text


def test_ns_residual_owner_predicates_and_reference_objects_are_parameters_not_fields():
    forbidden_field_names = [
        "ActualContinuumPopulatesCanonicalPair",
        "HighFrequencyPhysicalHeatEnvelopeWeld",
        "LowPhysicalMajorantDomination",
        "HighPhysicalMajorantDomination",
        "ContinuationCriterionLiteralNS",
        "PhysicalR440NoncoreCorePayment",
        "B1PhysicalProducer",
        "B2PhysicalProducer",
        "B3PhysicalProducer",
        "Q4IntegratedSpacetimeControl",
        "EPositiveGlobalAmplitudeControl",
        "Q5SignedQuinticFallback",
        "SelectedFamilyContinuationInputs",
        "IndependentKernelBuild",
        "IndependentDASHIReconstruction",
        "selectedPairData",
        "selectedHeatEnvelopeData",
        "selectedLowMajorant",
        "selectedHighMajorant",
        "selectedLowEnvelope",
        "selectedHighEnvelope",
    ]
    for path in CANONICAL_RESIDUAL_OWNERS:
        text = _read(path)
        field_blocks = re.findall(r"(?ms)^\s*field\s*\n(.*?)(?=^\S|\Z)", text)
        joined = "\n".join(field_blocks)
        for name in forbidden_field_names:
            assert not re.search(rf"(?m)^\s*{re.escape(name)}\s*:", joined)


def test_ns_a_and_b_residual_surfaces_match_current_nonround_frontier():
    required = {
        "NSCanonicalA1PhysicalPopulationResidualExact.agda": [
            "actualCanonicalPairPopulation",
            "highFrequencyHeatEnvelopeWeld",
        ],
        "NSCanonicalA2MajorantResidualExact.agda": [
            "lowPhysicalMajorantDomination",
            "highPhysicalMajorantDomination",
        ],
        "NSCanonicalA3ContinuationResidualExact.agda": [
            "continuationCriterionLiteralNS",
        ],
        "NSCanonicalB4PhysicalR440PaymentResidualExact.agda": [
            "physicalR440NoncoreCorePayment",
        ],
        "NSCanonicalB123PhysicalProducerResidualExact.agda": [
            "b1PhysicalProducer",
            "b2PhysicalProducer",
            "b3PhysicalProducer",
        ],
        "NSCanonicalB7IntegratedControlResidualExact.agda": [
            "preferredQ4EControl",
            "q5SignedQuinticFallback",
        ],
        "NSCanonicalBContinuationResidualExact.agda": [
            "selectedFamilyContinuationInputs",
        ],
        "NSCanonicalCDReleasedReconstructionResidualExact.agda": [
            "independentKernelBuild",
            "independentDASHIReconstruction",
        ],
    }
    for filename, names in required.items():
        text = _read(f"DASHI/Physics/Closure/{filename}")
        for name in names:
            assert name in text


def test_ns_round_extraction_receipt_is_failure_closed():
    text = _assert_round_free_safe_owner(
        "DASHI/Physics/Closure/NSRoundExtractionReceiptExact.agda"
    )
    for literal in [
        "roundsAuthoritativeByDefault = false",
        "extractionCreatesTheoremTruth = false",
        "statusCountsAreClayPayments = false",
        "negativeResultsPreserved = true",
        "unresolvedPackagesCountAsDischarged = false",
        "roundFilesArchivedOrDeleted = false",
        "clayPromotion = false",
        "task4ObservedPackageCount = 30885",
        "task4ObservedUnresolvedPackageCount = 19312",
    ]:
        assert literal in text


def test_ns_terminal_scheduler_uses_only_canonical_nonround_owners_and_false_gates():
    text = _assert_round_free_safe_owner(
        "DASHI/Physics/Closure/NSCanonicalClayResidualExact.agda"
    )
    imports = _import_lines(text)
    for path in CANONICAL_RESIDUAL_OWNERS:
        module = path.removesuffix(".agda").replace("/", ".")
        assert module in imports
    assert "Round" not in imports
    assert "clayNavierStokesPromoted = false" in text
    assert "clayPromotion = false" in text
    assert "as A1 using ()" in imports
    assert "as B4 using ()" in imports


def test_ns_terminal_scheduler_does_not_claim_unresolved_tail_is_discharged():
    text = _read("DASHI/Physics/Closure/NSCanonicalClayResidualExact.agda")
    assert "unresolvedPackagesDischarged = false" in text
    assert "19312" in text
    assert "5508" in text
    assert "582" in text
