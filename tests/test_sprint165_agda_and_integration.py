from __future__ import annotations

import re
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
PHYSICS_CLOSURE = REPO_ROOT / "DASHI" / "Physics" / "Closure"
OBLIGATION_INDEX = REPO_ROOT / "DASHI" / "Promotion" / "ObligationIndex.agda"
EVERYTHING = REPO_ROOT / "DASHI" / "Everything.agda"
README = REPO_ROOT / "README.md"
AGDA_TARGETS = REPO_ROOT / "Docs" / "AgdaValidationTargets.md"
LANE_PLAN = REPO_ROOT / "Docs" / "UnifiedRoutesLanePlan.md"

PIPELINE_MODULE = "DASHI.Physics.Closure.FiniteDepthBoundaryObservablePromotionPipeline"
PIPELINE_RECEIPT = PHYSICS_CLOSURE / "FiniteDepthBoundaryObservablePromotionPipeline.agda"

ADJACENT_RECEIPTS = {
    "bt_finite_hodge_effective_action": PHYSICS_CLOSURE
    / "BTFiniteHodgeEffectiveActionTheoremBoundary.agda",
    "bt_finite_hodge_star": PHYSICS_CLOSURE / "BTFiniteHodgeStarObligation.agda",
    "bt_finite_ym_gap_transfer": PHYSICS_CLOSURE
    / "BTFiniteBuildingYMGapTransferBoundary.agda",
    "bt_ns_boundary_defect": PHYSICS_CLOSURE
    / "BTNSBoundaryDefectLeakageTarget.agda",
}

PIPELINE_TARGET_TERMS = (
    "FiniteDepthBoundaryObservablePromotionPipeline",
    "finiteDepthBoundaryObservableCandidateCheckedAuthorityBlocked",
    "bulkFiniteSubspaceRow",
    "effectiveBoundaryActionRow",
    "boundaryObservableRow",
    "covarianceComparisonRow",
    "authorityReceiptRow",
    "holdoutProtocolRow",
    "promotionGuardRow",
    "BoundaryObservablePipelineResidual",
    "canonicalFiniteDepthBoundaryObservablePromotionPipeline",
    "canonicalFiniteDepthBoundaryObservablePipelineStepCountIs7",
)

PIPELINE_FALSE_FLAGS = (
    "fixtureBaselineAuthorityAccepted",
    "rawProviderVectorsBound",
    "acceptedAuthorityTokenPresent",
    "holdoutProtocolAccepted",
    "residualAuthorityAccepted",
    "empiricalValidationPromoted",
    "standardModelPromoted",
    "terminalPromotion",
)

ADJACENT_FALSE_FLAGS = {
    "bt_finite_hodge_effective_action": (
        "physicalMatterCurrentAuthorityAccepted",
        "realDStarFEqualsJLawPromoted",
        "maxwellPromoted",
        "yangMillsPromoted",
        "clayYangMillsPromoted",
        "terminalPromotion",
    ),
    "bt_finite_hodge_star": (
        "btMetricHodgeStarPromoted",
        "hodgeStarSquareLawPromoted",
        "finitePairingPromoted",
        "finiteIBPPromoted",
        "dStarFEqualsJPromoted",
        "dJZeroPromoted",
        "maxwellFieldEquationPromoted",
        "yangMillsPromoted",
        "terminalPromotion",
    ),
    "bt_finite_ym_gap_transfer": (
        "gaugeInvariantHilbertSpaceConstructed",
        "uniformFiniteBuildingLowerBoundProved",
        "continuumTransferPromoted",
        "spectralGapPromoted",
        "clayYangMillsPromoted",
        "terminalPromotion",
    ),
    "bt_ns_boundary_defect": (
        "FiniteDepthNSTopologicalLeakage",
        "DefectMeasureNearSigmaPSupportLemma",
        "PressureCoherentBoundaryDefectSectionLemma",
        "LeakageOrPressureCommutatorCostLemma",
        "UniformDepthLimitPassage",
        "ContinuumNavierStokesBridge",
        "full_clay_ns_solved",
        "fullClayNSSolved",
        "clayNavierStokesPromoted",
    ),
}

EXPECTED_INTEGRATION_IMPORTS = (
    "DASHI.Physics.Closure.BTFiniteHodgeEffectiveActionTheoremBoundary",
    "DASHI.Physics.Closure.BTFiniteHodgeStarObligation",
    "DASHI.Physics.Closure.BTFiniteBuildingYMGapTransferBoundary",
    "DASHI.Physics.Closure.BTNSBoundaryDefectLeakageTarget",
    PIPELINE_MODULE,
)


def read_text(path: Path) -> str:
    assert path.is_file(), f"missing {path.relative_to(REPO_ROOT)}"
    return path.read_text(encoding="utf-8", errors="replace")


def normalize(text: object) -> str:
    return re.sub(r"[^a-z0-9]+", "_", str(text).lower()).strip("_")


def assignment_to_value(text: str, name: str, value: bool) -> bool:
    expected = "true" if value else "false"
    patterns = (
        rf"\b{re.escape(name)}\s*:\s*Bool\s*\n\s*{re.escape(name)}\s*=\s*{expected}\b",
        rf";\s*{re.escape(name)}\s*=\s*{expected}\b",
        rf"\b{re.escape(name)}\s*=\s*{expected}\b",
        rf"\b{re.escape(name)}[A-Za-z0-9_']*Is{'True' if value else 'False'}\s*:\s*"
        rf"{re.escape(name)}\b[\s\S]*?\b{expected}\b",
    )
    return any(re.search(pattern, text) for pattern in patterns)


def assert_flag_false(text: str, name: str, label: str) -> None:
    assert assignment_to_value(text, name, False), f"{label} missing false flag: {name}"
    assert not assignment_to_value(text, name, True), f"{label} promotes unexpectedly: {name}"


def import_lines(text: str, module_name: str) -> list[str]:
    return re.findall(
        r"^\s*import\s+" + re.escape(module_name) + r"(?:\s+as\s+\w+)?\s*$",
        text,
        flags=re.MULTILINE,
    )


def test_sprint165_pipeline_receipt_has_exact_module_and_target_names() -> None:
    text = read_text(PIPELINE_RECEIPT)

    assert text.splitlines()[0] == f"module {PIPELINE_MODULE} where"
    for term in PIPELINE_TARGET_TERMS:
        assert term in text, term

    for term in (
        "finite-depth bulk subspace",
        "effective boundary action",
        "boundary observable",
        "covariance-aware comparison",
        "authority receipt",
        "holdout protocol",
        "promotion guard",
    ):
        assert term in text, term


def test_sprint165_pipeline_keeps_observable_promotion_flags_false() -> None:
    text = read_text(PIPELINE_RECEIPT)

    for name in PIPELINE_FALSE_FLAGS:
        assert_flag_false(text, name, "finite-depth observable pipeline")

    forbidden_true_names = [
        name
        for name in re.findall(r"\b([A-Za-z][A-Za-z0-9_']*)\s*=\s*true\b", text)
        if any(part in normalize(name) for part in ("authority", "holdout", "promoted", "promotion"))
    ]
    assert forbidden_true_names == []


def test_sprint165_adjacent_clay_ym_ns_maxwell_flags_remain_false() -> None:
    for label, path in ADJACENT_RECEIPTS.items():
        text = read_text(path)
        for name in ADJACENT_FALSE_FLAGS[label]:
            assert_flag_false(text, name, label)


def test_sprint165_everything_and_docs_integration_are_complete_once_started() -> None:
    everything = read_text(EVERYTHING)
    docs = {
        "README.md": read_text(README),
        "Docs/AgdaValidationTargets.md": read_text(AGDA_TARGETS),
        "Docs/UnifiedRoutesLanePlan.md": read_text(LANE_PLAN),
    }

    integration_started = (
        any(import_lines(everything, module_name) for module_name in EXPECTED_INTEGRATION_IMPORTS)
        or any(PIPELINE_MODULE in text for text in docs.values())
        or "FiniteDepthBoundaryObservablePromotionPipeline" in read_text(OBLIGATION_INDEX)
    )
    assert integration_started, "Sprint165 integration has not started in Everything/docs/ObligationIndex"

    for module_name in EXPECTED_INTEGRATION_IMPORTS:
        imports = import_lines(everything, module_name)
        assert imports == [f"import {module_name}"], (
            "DASHI/Everything.agda must import exactly once: " + module_name
        )

    for doc_name, text in docs.items():
        assert (
            PIPELINE_MODULE in text
            or "DASHI/Physics/Closure/FiniteDepthBoundaryObservablePromotionPipeline.agda"
            in text
        ), f"{doc_name} missing {PIPELINE_MODULE}"
        assert "Maxwell" in text, f"{doc_name} missing Maxwell boundary wording"
        assert "Yang-Mills" in text or "YM" in text, (
            f"{doc_name} missing Yang-Mills/YM boundary wording"
        )
        assert "NS" in text or "Navier-Stokes" in text or "BTNS" in text, (
            f"{doc_name} missing NS/Navier-Stokes boundary wording"
        )


def test_sprint165_obligation_index_integration_is_present_after_orchestrator_start() -> None:
    everything = read_text(EVERYTHING)
    obligation_index = read_text(OBLIGATION_INDEX)
    docs_text = "\n".join(read_text(path) for path in (README, AGDA_TARGETS, LANE_PLAN))

    orchestrator_started = (
        PIPELINE_MODULE in everything
        or PIPELINE_MODULE in docs_text
        or "FiniteDepthBoundaryObservablePromotionPipeline" in obligation_index
    )
    assert orchestrator_started, "Sprint165 orchestrator integration has not started"

    normalized_index = normalize(obligation_index)
    for term in (
        "FiniteDepthBoundaryObservablePromotionPipeline",
        "BTFiniteHodgeEffectiveActionTheoremBoundary",
        "BTFiniteHodgeStarObligation",
        "BTFiniteBuildingYMGapTransferBoundary",
        "BTNSBoundaryDefectLeakageTarget",
        "finite depth boundary observable",
        "maxwell",
        "yang mills",
        "navier stokes",
        "promotesClaim",
    ):
        assert normalize(term) in normalized_index, (
            "DASHI/Promotion/ObligationIndex.agda missing Sprint165 integration term: "
            + term
        )

    assert re.search(r"\bpromotesClaim\s*=\s*false\b", obligation_index)
    assert not re.search(r"\bpromotesClaim\s*=\s*true\b", obligation_index)
