from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
YM = ROOT / "DASHI/Physics/YangMills"

INSTANTIATION = YM / "BalabanCMP109CanonicalResidualInstantiationExact.agda"
OWNER = YM / "BalabanCMP109CanonicalSourceSemanticsObligationsExact.agda"
RECEIPT = YM / "BalabanCMP109ResidualInstantiationReceiptExact.agda"
CLAY = YM / "YangMillsCanonicalClayResidualExact.agda"


def _read(path: Path) -> str:
    assert path.exists(), f"missing {path}"
    text = path.read_text(encoding="utf-8")
    imports = "\n".join(
        line for line in text.splitlines()
        if line.lstrip().startswith(("open import", "import"))
    )
    assert "Round" not in imports
    assert "{!!}" not in text
    assert "postulate" not in text
    assert "--allow-unsolved-metas" not in text
    assert "{-# OPTIONS --safe #-}" in text
    assert "clayPromotion = true" not in text
    assert "clayYangMillsPromoted = true" not in text
    return text


def test_cmp109_instantiation_classifies_all_three_blockers():
    text = _read(INSTANTIATION)
    assert "data CMP109BlockerKind" in text
    assert "sourceReconstructionMissing" in text
    assert "sameObjectAttachmentMissing" in text
    assert "transportEqualityMissing" in text
    assert "generatedHistoryResponseBlocker = sourceReconstructionMissing" in text
    assert "betaDifferenceBlocker = sameObjectAttachmentMissing" in text
    assert "physicalCompositeD1Blocker = transportEqualityMissing" in text


def test_beta_difference_is_structurally_discharged_by_existing_nonround_theorem():
    text = _read(INSTANTIATION)
    assert "BalabanBetaPrefixSensitivityToTubeContractionExact" in text
    assert "selectedBetaDifferenceDecomposition" in text
    assert "Prefix.sourceMapDifferenceIsBetaDifference" in text
    assert "SelectedCMP109BetaDifferenceAttachment" in text


def test_generated_history_response_is_sharpened_to_existing_nonround_producer():
    text = _read(INSTANTIATION)
    assert "BalabanYM4WardQuarticResponseProducerAdapterExact" in text
    assert "CMP109GeneratedHistoryResponseResidual" in text
    assert "Producer.WardQuarticResponseProducer" in text
    assert "literalGeneratedHistoryResponseProducer" in text


def test_all_cmp109_payments_are_attached_to_one_selected_source():
    text = _read(INSTANTIATION)
    assert "(selectedSource : SelectedSource)" in text
    assert "ProducerBelongsToSelectedSource" in text
    assert "producerBelongsToSelectedSource" in text
    assert "ShootingMapBelongsToSelectedSource" in text
    assert "shootingMapBelongsToSelectedSource" in text
    assert "D1BelongsToSelectedSource" in text
    assert "physicalCompositeD1BelongsToSelectedSource" in text
    assert "substitutedD1BelongsToSelectedSource" in text


def test_physical_composite_d1_is_sharpened_to_transport_equality():
    text = _read(INSTANTIATION)
    assert "PhysicalCompositeD1TransportResidual" in text
    assert "physicalCompositeD1" in text
    assert "substitutedD1" in text
    assert "physicalCompositeD1IsSubstitutedD1" in text
    assert "DASHI extension" in text


def test_source_attribution_boundaries_are_explicit():
    text = _read(INSTANTIATION)
    assert "10.1007/BF01215223" in text
    assert "10.1007/BF01217741" in text
    assert "10.1007/BF01238433" in text
    assert "DASHI EXTENSION" in text


def test_cmp109_canonical_owner_uses_sharpened_residual_types():
    text = _read(OWNER)
    assert "BalabanCMP109CanonicalResidualInstantiationExact" in text
    assert "CMP109CanonicalSourceSemanticsObligations" in text
    assert "CMP109GeneratedHistoryResponseResidual selectedSource cutoff" in text
    assert "SelectedCMP109BetaDifferenceAttachment selectedSource TubePoint" in text
    assert "PhysicalCompositeD1TransportResidual" in text
    assert "selectedSource Component Background Tangent Scalar" in text


def test_cmp109_receipt_records_paid_and_unpaid_boundaries():
    text = _read(RECEIPT)
    assert "betaDifferenceAlgebraStructurallyPaid = true" in text
    assert "betaDifferenceStillNeedsSelectedAttachment = true" in text
    assert "generatedHistoryResponseStillNeedsSourceReconstruction = true" in text
    assert "physicalCompositeD1StillNeedsTransportEquality = true" in text
    assert "genuinelyNewMathematicsEstablished = false" in text
    assert "clayPromotion = false" in text


def test_clay_residual_consumes_sharpened_cmp109_owner_and_stays_closed():
    text = _read(CLAY)
    assert "(selectedSource : SelectedSource)" in text
    assert "CMP109.CMP109CanonicalSourceSemanticsObligations" in text
    assert "selectedSource TubePoint cutoff Component Background Tangent Scalar" in text
    assert "clayYangMillsPromoted = false" in text
    assert "clayPromotion = false" in text
