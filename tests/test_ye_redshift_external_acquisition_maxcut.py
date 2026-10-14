from __future__ import annotations

from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
DASHI = REPO_ROOT / "DASHI"
MODULE = DASHI / "Physics" / "Closure" / "BothwellYe2022ExternalAcquisitionMaxCut.agda"
STATUS = DASHI / "Physics" / "Closure" / "QuantumClockEmpiricalRedshiftIngestionStatusExact.agda"
ROLLUP = DASHI / "Physics" / "Closure" / "YeRedshiftEverything.agda"


def read(path: Path) -> str:
    assert path.is_file(), f"missing {path.relative_to(REPO_ROOT)}"
    return path.read_text(encoding="utf-8")


def test_packet_targets_real_corresponding_authors_and_external_rows() -> None:
    text = read(MODULE)
    for marker in (
        "tobias.bothwell@colorado.edu",
        "ye@jila.colorado.edu",
        "sourceArtifactSha256Field",
        "rawMeasurementField",
        "rawUncertaintyField",
        "systematicsBudgetField",
        "covarianceOrIndependenceField",
        "fourteen fitted gradients",
        "position-resolved",
        "analysis code",
    ):
        assert marker in text


def test_packet_separates_author_evidence_from_internal_ingestion_work() -> None:
    text = read(MODULE)
    for marker in (
        "requestPacketConstructed = true",
        "authorRequestSent = false",
        "authorReplyReceived = false",
        "rawExperimentArraysAcquired = false",
        "analysisCodeAcquired = false",
        "byteChecksumComputedAfterAcquisition = false",
        "analysisReplayCompleted = false",
        "genericAcceptanceTokenConstructed = false",
        "consumerIngestionIsInternalPostAcquisition = true",
    ):
        assert marker in text


def test_packet_does_not_re_request_already_paid_public_coordinates() -> None:
    text = read(MODULE)
    for marker in (
        "sourceArtifactIdentityAlreadyPaid = true",
        "sourceAccessDateAlreadyPaid = true",
        "gravitationalPotentialModelAlreadyPaid = true",
        "publishedSystematicsSummaryAlreadyPaid = true",
        "requestPacketIsEvidence = false",
    ):
        assert marker in text


def test_status_and_rollup_expose_acquisition_packet_without_promotion() -> None:
    status = read(STATUS)
    for marker in (
        "externalAcquisitionPacketConstructed = true",
        "externalAuthorRequestSent = false",
        "genericAcceptanceTokenConstructed = false",
        "terminalSIMetrologyPromotionAllowed = false",
    ):
        assert marker in status

    rollup = read(ROLLUP)
    line = "import DASHI.Physics.Closure.BothwellYe2022ExternalAcquisitionMaxCut"
    assert rollup.count(line) == 1
