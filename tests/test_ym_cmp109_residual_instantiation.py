from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
YM = ROOT / "DASHI/Physics/YangMills"

INSTANTIATION = YM / "BalabanCMP109CanonicalResidualInstantiationExact.agda"
BETA_BRIDGE = YM / "BalabanCMP109BetaDifferenceRealAnalysisBridgeExact.agda"
OWNER = YM / "BalabanCMP109CanonicalSourceSemanticsObligationsExact.agda"
RECEIPT = YM / "BalabanCMP109ResidualInstantiationReceiptExact.agda"
CLAY = YM / "YangMillsCanonicalClayResidualExact.agda"


def _raw(path: Path) -> str:
    assert path.exists(), f"missing {path}"
    text = path.read_text(encoding="utf-8")
    imports = "\n".join(
        line for line in text.splitlines()
        if line.lstrip().startswith(("open import", "import"))
    )
    assert "Round" not in imports
    assert "{!!}" not in text
    assert not re.search(r"(?m)^\s*postulate\b", text)
    assert "--allow-unsolved-metas" not in text
    assert "clayPromotion = true" not in text
    assert "clayYangMillsPromoted = true" not in text
    return text


def _read_safe(path: Path) -> str:
    text = _raw(path)
    assert "{-# OPTIONS --safe #-}" in text
    return text


def test_cmp109_instantiation_classifies_all_three_blockers():
    text = _read_safe(INSTANTIATION)
    assert "data CMP109BlockerKind" in text
    assert "sourceReconstructionMissing" in text
    assert "sameObjectAttachmentMissing" in text
    assert "transportEqualityMissing" in text
    assert "generatedHistoryResponseBlocker = sourceReconstructionMissing" in text
    assert "betaDifferenceBlocker = sameObjectAttachmentMissing" in text
    assert "physicalCompositeD1Blocker = transportEqualityMissing" in text


def test_safe_instantiation_does_not_import_postulated_real_analysis_lane():
    text = _read_safe(INSTANTIATION)
    assert "RealAnalysisAxioms" not in text
    assert "BalabanBetaPrefixSensitivityToTubeContractionExact" not in text
    assert "BalabanYM4WardQuarticResponseProducerAdapterExact" not in text


def test_beta_difference_application_is_isolated_in_explicit_nonsafe_bridge():
    text = _raw(BETA_BRIDGE)
    assert "{-# OPTIONS --safe #-}" not in text
    assert "RealAnalysisAxioms" in text
    assert "BalabanBetaPrefixSensitivityToTubeContractionExact" in text
    assert "Prefix.sourceMapDifferenceIsBetaDifference" in text
    assert "betaDifferencePaidRelativeToRealAnalysisAxioms" in text


def test_attachment_relations_are_external_parameters_not_residual_fields():
    text = _read_safe(INSTANTIATION)
    for relation_name in (
        "ProducerBelongsToSelectedSource",
        "ShootingMapBelongsToSelectedSource",
        "D1BelongsToSelectedSource",
    ):
        assert relation_name in text
    assert not re.search(
        r"(?m)^\s{4}[A-Za-z0-9_]*BelongsToSelectedSource\s*:", text
    )
    assert not re.search(r"(?m)^\s{4}substitutedD1\s*:", text)
    assert not re.search(r"(?m)^\s{4}physicalCompositeD1\s*:", text)


def test_generated_history_response_keeps_externally_fixed_producer_carrier():
    text = _read_safe(INSTANTIATION)
    assert "CMP109GeneratedHistoryResponseResidual" in text
    assert "(Producer : Set)" in text
    assert "(ProducerBelongsToSelectedSource : SelectedSource → Producer → Set)" in text
    assert "literalGeneratedHistoryResponseProducer : Producer" in text
    assert "producerAttachment" in text


def test_beta_attachment_keeps_externally_fixed_shooting_interface():
    text = _read_safe(INSTANTIATION)
    assert "SelectedCMP109BetaDifferenceAttachment" in text
    assert "(TubePoint ShootingMap Scalar : Set)" in text
    assert "(ShootingMapBelongsToSelectedSource" in text
    assert "selectedShootingMap : ShootingMap" in text
    assert "shootingMapAttachment" in text


def test_physical_composite_d1_reference_functions_and_attachments_are_parameters():
    text = _read_safe(INSTANTIATION)
    assert "PhysicalCompositeD1TransportResidual" in text
    assert "(physicalCompositeD1 substitutedD1 :" in text
    assert "(D1BelongsToSelectedSource :" in text
    assert "(physicalCompositeD1Attachment :" in text
    assert "(substitutedD1Attachment :" in text
    assert "physicalCompositeD1IsSubstitutedD1" in text
    assert "DASHI EXTENSIONS" in text


def test_source_attribution_boundaries_are_explicit():
    text = _read_safe(INSTANTIATION)
    assert "10.1007/BF01215223" in text
    assert "10.1007/BF01217741" in text
    assert "10.1007/BF01238433" in text
    assert "DASHI EXTENSIONS" in text


def test_cmp109_canonical_owner_uses_sharpened_external_parameters():
    text = _read_safe(OWNER)
    assert "BalabanCMP109CanonicalResidualInstantiationExact" in text
    assert "CMP109CanonicalSourceSemanticsObligations" in text
    assert "CMP109GeneratedHistoryResponseResidual" in text
    assert "SelectedCMP109BetaDifferenceAttachment" in text
    assert "PhysicalCompositeD1TransportResidual" in text
    assert "ProducerBelongsToSelectedSource" in text
    assert "ShootingMapBelongsToSelectedSource" in text
    assert "D1BelongsToSelectedSource" in text


def test_cmp109_receipt_records_relative_axiom_boundary_and_unpaid_residuals():
    text = _read_safe(RECEIPT)
    assert "betaDifferenceAlgebraPaidRelativeToRealAnalysisAxioms = true" in text
    assert "betaDifferenceAlgebraUnconditionallySafePaid = false" in text
    assert "betaDifferenceStillNeedsSelectedAttachment = true" in text
    assert "generatedHistoryResponseStillNeedsSourceReconstruction = true" in text
    assert "physicalCompositeD1StillNeedsTransportEquality = true" in text
    assert "genuinelyNewMathematicsEstablished = false" in text
    assert "clayPromotion = false" in text


def test_clay_residual_uses_qualified_only_owner_imports_and_stays_closed():
    text = _read_safe(CLAY)
    for alias in ("CMP109", "TransferGap", "R409", "R429", "Gap", "Limit"):
        assert f" as {alias} using ()" in text
    assert "CMP109.CMP109CanonicalSourceSemanticsObligations" in text
    assert "clayYangMillsPromoted = false" in text
    assert "clayPromotion = false" in text
