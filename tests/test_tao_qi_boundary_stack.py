from __future__ import annotations

from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]


def assert_any_marker(text: str, markers: tuple[str, ...]) -> None:
    assert any(marker in text for marker in markers), markers


def test_everything_imports_tao_qi_boundary_stack() -> None:
    text = (REPO_ROOT / "DASHI" / "Everything.agda").read_text(encoding="utf-8")

    required_imports = {
        "import DASHI.Culture.TaoChapterReadingReceipt",
        "import DASHI.Culture.TaoOperatorGrammar",
        "import DASHI.Culture.YinYangPolarityBoundary",
        "import DASHI.Culture.YinYangSymbolGeometryBoundary",
        "import DASHI.Interop.TaoYinYangAdapter",
        "import DASHI.Interop.YinYangQiAdapter",
        "import DASHI.Interop.PolarityPhaseFieldBridge",
        "import DASHI.Interop.PolarityBettiSupportBoundary",
        "import DASHI.Interop.BettiQiAdapter",
        "import DASHI.Interop.CarryCompletionSpectralBridge",
        "import DASHI.Interop.TaoQiReadingAdapter",
        "import DASHI.Interop.TaoMeditationQiAdapter",
        "import DASHI.Promotion.PolarityFieldObligationIndex",
        "import DASHI.Promotion.TaoQiObligationIndex",
    }

    for marker in required_imports:
        assert marker in text, marker


def test_promotion_index_references_tao_qi_boundary_surface() -> None:
    text = (REPO_ROOT / "DASHI" / "Promotion" / "ObligationIndex.agda").read_text(
        encoding="utf-8"
    )

    assert "taoQiBoundaryLane" in text
    assert "polarityFieldBoundaryLane" in text
    assert "bettiSupportBoundaryLane" in text
    assert (
        "import DASHI.Promotion.PolarityFieldObligationIndex as PolarityFieldBoundary"
        in text
    )
    assert "import DASHI.Promotion.TaoQiObligationIndex as TaoQiBoundary" in text
    assert '"DASHI.Culture.YinYangSymbolGeometryBoundary"' in text
    assert '"canonicalYinYangSymbolGeometryBoundaryReceipt"' in text
    assert '"DASHI.Promotion.PolarityFieldObligationIndex"' in text
    assert '"canonicalPolarityFieldObligationIndexReceipt"' in text
    assert '"DASHI.Promotion.TaoQiObligationIndex"' in text
    assert '"canonicalTaoQiObligationIndexReceipt"' in text
    assert '"DASHI.Interop.PolarityBettiSupportBoundary"' in text
    assert '"canonicalPolarityBettiSupportBoundary"' in text
    assert "crossDomainInterpretationBoundaryCount = 27" in text


def test_tao_qi_obligation_module_mentions_full_bridge_stack() -> None:
    text = (REPO_ROOT / "DASHI" / "Promotion" / "TaoQiObligationIndex.agda").read_text(
        encoding="utf-8"
    )

    assert "Tao / Qi obligation index" in text
    assert "candidate-only payload" in text or "candidate-only" in text
    assert "canonicalTaoSourceReceipt" in text
    assert "canonicalTaoOperatorGrammarReceipt" in text
    assert "canonicalYinYangPolarityBoundaryReceipt" in text
    assert "canonicalYinYangSymbolGeometryBoundaryReceipt" in text
    assert "canonicalTaoYinYangBridgeReceipt" in text
    assert "canonicalYinYangQiBridgeReceipt" in text
    assert "canonicalPolarityPhaseFieldBridge" in text
    assert "canonicalBettiSupportBoundaryModuleName" in text
    assert "canonicalBettiSupportBoundarySurfaceName" in text
    assert "canonicalBettiQiAdapterModuleName" in text
    assert "canonicalBettiQiAdapterSurfaceName" in text
    assert "canonicalQiOperatorTheoryBoundaryReceipt" in text
    assert "canonicalQiCarrierFieldBridgeReceipt" in text
    assert "canonicalTaoQiBridgeReceipt" in text
    assert "canonicalTaoMeditationQiBridgeReceipt" in text
    assert "canonicalPolarityFieldObligationIndexReceipt" in text


def test_recovered_boundary_geometry_and_polarity_slice_markers() -> None:
    geometry_text = (
        REPO_ROOT / "DASHI" / "Culture" / "YinYangSymbolGeometryBoundary.agda"
    ).read_text(encoding="utf-8")
    polarity_text = (
        REPO_ROOT / "DASHI" / "Culture" / "YinYangPolarityBoundary.agda"
    ).read_text(encoding="utf-8")

    assert_any_marker(
        geometry_text,
        (
            "candidateOnlyGeometryBoundary",
            "canonicalYinYangGeometryAuthorityBits",
            "canonicalLargeEnclosingCircleEquation",
            "canonicalTeardropARow",
            "canonicalYangRegionRow",
            "canonicalUpperSCurveRow",
            "boundaryPolicySummary",
        ),
    )
    assert "31 + 0 + 1 body/boundary/seed ledger" in geometry_text
    assert (
        "Candidate-only Cartesian and set-theoretic geometry boundary for the yin-yang symbol, now carrying a 31 + 0 + 1 body/boundary/seed ledger alongside the S-curve boundary rows."
        in geometry_text
    )
    assert_any_marker(
        polarity_text,
        (
            "canonicalYinYangPolarityBoundaryRows",
            "canonicalYinYangGeometrySupportReference",
            "boundaryRowsAreCanonical",
            "geometrySupportReferenceIsCanonical",
            "boundaryRowCountMatchesCanonical",
            "canonicalYinYangPolarityBoundaryReceipt",
        ),
    )
    assert (
        "Candidate-only yin/yang symbol geometry support surface covering enclosing-circle, inner-circle, eye-dot, teardrop, and S-curve boundary readings."
        in polarity_text
    )
    assert "boundaryRowCount" in polarity_text
    assert "geometrySupportReference" in polarity_text


def test_recovered_31_plus_0_plus_1_phase_field_slice_markers() -> None:
    field_bridge_text = (
        REPO_ROOT
        / "DASHI"
        / "Physics"
        / "Closure"
        / "SSPPrimeLane369FieldPhaseBridge.agda"
    ).read_text(encoding="utf-8")
    phase_bridge_text = (
        REPO_ROOT / "DASHI" / "Interop" / "PolarityPhaseFieldBridge.agda"
    ).read_text(encoding="utf-8")

    assert_any_marker(
        field_bridge_text,
        (
            "bodySurfaceBridge",
            "residueSurfaceBridge",
            "focusBodySurface",
            "focusResidueSurface",
            "canonicalRootFieldPhaseBridge",
            "canonicalDepth3FieldPhaseBridge",
            "canonicalRootFieldBodyReceipt",
            "canonicalDepth3FieldResidueReceipt",
        ),
    )
    assert "Base369 readouts for the focused body and residue surfaces" in field_bridge_text
    assert_any_marker(
        phase_bridge_text,
        (
            "canonicalYangPhaseCarrierRow",
            "canonicalYinPhaseCarrierRow",
            "canonicalBalancedPhaseCarrierRow",
            "canonicalYangSupportGeometry",
            "canonicalYinYangSupervoxel",
            "canonicalYinYangWave",
            "canonicalYinYangSuperposition",
            "candidate-only bridge from yin/yang polarity into 369 phase rows",
        ),
    )
    assert "support geometry" in phase_bridge_text
    assert "superposition candidates" in phase_bridge_text
    assert "blocked authority governance" in phase_bridge_text


def test_carry_completion_bridge_and_stage12_fibre_markers() -> None:
    carry_bridge_text = (
        REPO_ROOT / "DASHI" / "Interop" / "CarryCompletionSpectralBridge.agda"
    ).read_text(encoding="utf-8")
    stage_quotient_text = (
        REPO_ROOT / "DASHI" / "Algebra" / "StageQuotient.agda"
    ).read_text(encoding="utf-8")

    assert_any_marker(
        carry_bridge_text,
        (
            "threeAdicCompletionReceipt",
            "moonshineCarrySeedReceipt",
            "stageQuotientReceipt",
            "generalizedStage12Receipt",
            "canonicalCarryCompletionSpectralBridgeReceipt",
            "atlas11CarryDepthIsRev2",
        ),
    )
    assert "196883 + 1 = 196884" in carry_bridge_text
    assert "q(next overflow) fails to commute with rotateTri" in carry_bridge_text
    assert_any_marker(
        stage_quotient_text,
        (
            "Stage12FibreSurface",
            "canonicalStage12FibreSurface",
            "atlasRowsAreCanonical",
            "carry-depth",
            "fibre-of-quotient",
            "successor-non-equivariant",
        ),
    )


def test_stage12_fibre_surface_carry_depth_seam_hits_irreversibility_boundary() -> None:
    stage_quotient_text = (
        REPO_ROOT / "DASHI" / "Algebra" / "StageQuotient.agda"
    ).read_text(encoding="utf-8")
    boundary_text = (
        REPO_ROOT
        / "DASHI"
        / "Algebra"
        / "StageQuotientIrreversibilityBoundary.agda"
    ).read_text(encoding="utf-8")
    locator_text = (
        REPO_ROOT
        / "DASHI"
        / "Promotion"
        / "ExternalTheoremAuthoritySourceLocator.agda"
    ).read_text(encoding="utf-8")
    carry_bridge_text = (
        REPO_ROOT / "DASHI" / "Interop" / "CarryCompletionSpectralBridge.agda"
    ).read_text(encoding="utf-8")

    assert "carry-depth-seam" in stage_quotient_text
    assert "canonicalStage12FibreSurface" in stage_quotient_text
    assert "StageQuotientIrreversibilityBoundary" in boundary_text
    assert "irreversibilityCause" in boundary_text
    assert "nonInjectiveQuotient" in boundary_text
    assert "stageQuotientIrreversibilityBoundaryAnchor" in locator_text
    assert "Located at the StageQuotient irreversibility boundary" in locator_text
    assert "Stage12FibreSurface preserves atlas-11 as a seam with carry-depth rev-2" in carry_bridge_text
    assert "StageQuotient.Stage12FibreSurface.carry-depth" in carry_bridge_text


def test_recovered_carry_and_successor_adapter_slice_markers() -> None:
    yin_yang_qi_text = (
        REPO_ROOT / "DASHI" / "Interop" / "YinYangQiAdapter.agda"
    ).read_text(encoding="utf-8")
    tao_yin_yang_text = (
        REPO_ROOT / "DASHI" / "Interop" / "TaoYinYangAdapter.agda"
    ).read_text(encoding="utf-8")
    tao_qi_text = (
        REPO_ROOT / "DASHI" / "Interop" / "TaoQiReadingAdapter.agda"
    ).read_text(encoding="utf-8")

    assert_any_marker(
        yin_yang_qi_text,
        (
            "seedAttention",
            "seedThreshold",
            "carryBreath",
            "carryBody",
            "carryMemory",
            "carryResidual",
            "boundaryThreshold",
            "boundaryRelation",
            "bodyMovement",
            "bodyPosture",
        ),
    )
    assert_any_marker(
        yin_yang_qi_text,
        (
            "canonicalYinYangPolarityRowKinds",
            "rowKindProfile",
            "rowKindStatement",
            "canonicalYinYangQiAuthorityClosure",
            "canonicalYinYangQiBridgeReceipt",
        ),
    )
    assert_any_marker(
        tao_yin_yang_text,
        (
            "chapter1YinBoundaryRow",
            "chapter2YangComplementarityRow",
            "chapter6YinValleyRow",
            "chapter8YinWaterRow",
            "candidateInteropOnlyTrue",
            "canonicalTaoYinYangAuthorityBits",
            "canonicalTaoYinYangGovernance",
        ),
    )
    assert_any_marker(
        tao_qi_text,
        (
            "gateThresholdRow",
            "valleyLandscapeRow",
            "breathCarrierRow",
            "stillnessMeditationRow",
            "waterFlowRow",
            "desireReductionRow",
            "complementarityRow",
            "softnessSpectralRow",
            "canonicalTaoQiAdapterRows",
            "qiCarrierBridgeIsCanonical",
        ),
    )
    assert "boundary-gate grammar" in tao_qi_text
    assert "candidate-only Qi carrier, role, and formal-lens grammar" in tao_qi_text


def test_tao_source_receipt_mentions_external_lean_formalism() -> None:
    text = (REPO_ROOT / "DASHI" / "Culture" / "TaoChapterReadingReceipt.agda").read_text(
        encoding="utf-8"
    )

    assert "taoLeanPastebinUrl" in text
    assert "https://pastebin.xware.online/paste/20260621_131250_taoteching_lean" in text
    assert "canonicalTaoExternalFormalismSource" in text
    assert "canonicalTaoSourceProvenanceSurface" in text


def test_polarity_field_index_mentions_actual_middle_layer_modules() -> None:
    text = (
        REPO_ROOT / "DASHI" / "Promotion" / "PolarityFieldObligationIndex.agda"
    ).read_text(encoding="utf-8")

    assert "DASHI.Culture.YinYangPolarityBoundary" in text
    assert "DASHI.Culture.YinYangSymbolGeometryBoundary" in text
    assert "DASHI.Interop.TaoYinYangAdapter" in text
    assert "DASHI.Interop.YinYangQiAdapter" in text
    assert "DASHI.Interop.PolarityPhaseFieldBridge" in text
    assert "DASHI.Interop.PolarityBettiSupportBoundary" in text
    assert "DASHI.Interop.BettiQiAdapter" in text
    assert "canonicalYinYangSymbolGeometryBoundaryReceipt" in text
    assert "canonicalPolarityBettiSupportBoundaryReceipt" in text
    assert "canonicalBettiQiBridgeReceipt" in text
    assert "canonicalPolarityFieldObligationIndexReceipt" in text
