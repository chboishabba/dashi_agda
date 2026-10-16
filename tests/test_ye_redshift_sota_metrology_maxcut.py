from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CLOSURE = ROOT / "DASHI" / "Physics" / "Closure"

ZHENG = CLOSURE / "ZhengKolkowitz2023PublicDataReceiptExact.agda"
CGPM = CLOSURE / "CGPM2026OpticalSecondRelativisticBridgeExact.agda"
SOTA = CLOSURE / "OpticalClockChronometricGeodesySOTA2026Exact.agda"
DISCRIMINATOR = CLOSURE / "QuantumClockMetricResponseDiscriminatorCompilerExact.agda"
CURRENT = CLOSURE / "QuantumClockEmpiricalRedshiftIngestionStatus20261016Exact.agda"
ROLLUP = CLOSURE / "YeRedshiftEverything.agda"


def read(path: Path) -> str:
    assert path.is_file(), f"missing {path.relative_to(ROOT)}"
    return path.read_text(encoding="utf-8")


def test_zheng_2023_public_manifest_is_source_bounded() -> None:
    text = read(ZHENG)
    for marker in (
        "10.1038/s41467-023-40629-8",
        "10.5281/zenodo.8184043",
        "fiveEnsembleClockNetwork = true",
        "totalVerticalSpanMillimetres = 10",
        "publishedMeasuredGradientTenthsE19PerCm = 124",
        "publishedExpectedGradientTenthsE19PerCm = 109",
        "a829e2044f0ef2dd450435d7b790e8c7",
        "8edb5d957e81a07b07e9d350afe43e3a",
        "257eab6f29cf3480c536cac73ed3998a",
        "53987b91b94d75d844f865ac0a778e75",
        "publicProcessDataManifestIngested = true",
        "datasetBytesMaterialisedInRepo = false",
        "numericalReplayCompleted = false",
        "analysisCodePubliclyAvailable = false",
        "doesNotFillBothwellYeRawRows = true",
    ):
        assert marker in text


def test_cgpm_2026_bridge_keeps_policy_authority_separate() -> None:
    text = read(CGPM)
    for marker in (
        "10.59161/CGPM2026RES4E",
        "2026-10-15",
        "proposalTargetMeeting = \"29th CGPM (2030)\"",
        "opticalStandardsOutperformCurrentPrimaryRealization = true",
        "targetComparisonUncertaintyOrder = \"approaching 1e-18\"",
        "cgpmPolicyAuthorityIngested = true",
        "bothwellYeEstablishesCGPMPolicy = false",
        "cgpmResolutionEstablishesBothwellYeExperiment = false",
        "futureSecondRedefinitionAlreadyImplemented = false",
    ):
        assert marker in text


def test_sota_atlas_keeps_deployment_geodesy_and_transfer_distinct() -> None:
    text = read(SOTA)
    for marker in (
        "10.1103/PhysRevApplied.21.L061001",
        "longBaselineKilometres = 457",
        "heightEquivalentUncertaintyCentimetres = 27",
        "10.1038/s41467-025-61140-2",
        "unsupervisedSeaOperationDays = 21",
        "arXiv:2608.01916",
        "transportableRatioFractionalUncertaintyE18Tenths = 43",
        "transportableResultIsPreprint = true",
        "deploymentRobustnessIsNotChronometricAccuracy = true",
        "frequencyTransferIsNotGeopotentialKnowledge = true",
    ):
        assert marker in text


def test_metric_response_compiler_is_a_discriminator_not_exotic_evidence() -> None:
    text = read(DISCRIMINATOR)
    for marker in (
        "ordinaryGravityReferenceAvailable = true",
        "candidatePredictionNeedsSameObjectIntervention = true",
        "candidateMetricResponseObserved = false",
        "candidateModelValidated = false",
        "clockResidualCanBeDeclaredConsumer = true",
        "referenceCalibrationDoesNotPromoteMechanism = true",
    ):
        assert marker in text


def test_current_status_layers_sent_event_sota_and_fail_closed_evidence() -> None:
    text = read(CURRENT)
    for marker in (
        "authorRequestSent = true",
        "authorReplyReceived = false",
        "zhengPublicManifestAvailable = true",
        "zhengReplayCompleted = false",
        "cgpm2026MetrologyAuthorityAvailable = true",
        "bothwellYeRawReplayCompleted = false",
        "terminalEmpiricalPromotionAllowed = false",
    ):
        assert marker in text

    rollup = read(ROLLUP)
    for line in (
        "import DASHI.Physics.Closure.BothwellYe2022AuthorCorrespondenceReceiptExact",
        "import DASHI.Physics.Closure.ZhengKolkowitz2023PublicDataReceiptExact",
        "import DASHI.Physics.Closure.CGPM2026OpticalSecondRelativisticBridgeExact",
        "import DASHI.Physics.Closure.OpticalClockChronometricGeodesySOTA2026Exact",
        "import DASHI.Physics.Closure.QuantumClockMetricResponseDiscriminatorCompilerExact",
        "import DASHI.Physics.Closure.QuantumClockEmpiricalRedshiftIngestionStatus20261016Exact",
    ):
        assert rollup.count(line) == 1
