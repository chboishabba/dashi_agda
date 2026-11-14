from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def text(path: str) -> str:
    return (ROOT / path).read_text(encoding="utf-8")


def test_terminal_source_maxcut_records_paid_rt_and_jacobson_layers():
    p = text("DASHI/Quantum/QuantumBirthmarkHolographyGravityTerminalMaxCut20261012Exact.agda")
    for token in [
        "correctedFiniteRTEntropyPaid",
        "zModCarrierFactorizationPaid",
        "correctedZModStatePaid",
        "upstreamStateContractNoGoPaid",
        "unruhScalarNormalizationPaid",
        "raychaudhuriEquilibriumAlgebraPaid",
        "horizonFluxAreaReductionPaid",
        "localFrameFieldCompilerPaid",
        "pointwiseEinsteinLambdaPaid",
        "sameObjectRecoveredLambdaConstancyCompilerPaid",
    ]:
        assert token in p


def test_terminal_source_maxcut_leaves_only_external_same_object_payments():
    p = text("DASHI/Quantum/QuantumBirthmarkHolographyGravityTerminalMaxCut20261012Exact.agda")
    for token in [
        "upstreamTreeContractionReplacementOrEquivalenceStillRequired",
        "geometricSubtreeMinimalCutIdentificationStillRequired",
        "physicalBulkBoundaryDictionaryStillRequired",
        "physicalBirthmarkFactorizationStillRequired",
        "physicalBisognanoWichmannKMSStillRequired",
        "physicalEntropyAreaReceiptStillRequired",
        "physicalHorizonCongruenceStressReceiptStillRequired",
        "physicalBianchiStressConservationStillRequired",
        "continuumEinsteinMatterAttachmentStillRequired",
        "empiricalValidationStillRequired",
        "exactHeadKernelReceiptsStillRequired",
    ]:
        assert token in p


def test_rollup_registers_terminal_source_maxcut():
    p = text("DASHI/Quantum/Everything.agda")
    assert "import DASHI.Quantum.QuantumBirthmarkHolographyGravityTerminalMaxCut20261012Exact" in p
