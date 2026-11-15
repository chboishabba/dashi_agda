from __future__ import annotations

from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
DASHI = REPO_ROOT / "DASHI"
MODULE = DASHI / "Physics" / "Closure" / "BothwellYe2022ExternalAcquisitionMaxCut.agda"
SENT = DASHI / "Physics" / "Closure" / "BothwellYe2022AuthorCorrespondenceReceiptExact.agda"
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


def test_packet_preserves_historical_construction_state() -> None:
    text = read(MODULE)
    for marker in (
        "requestPacketConstructed = true",
        "authorRequestSent = false",
        "requestPacketIsEvidence = false",
        "genericAcceptanceTokenConstructed = false",
    ):
        assert marker in text


def test_later_provider_backed_send_receipt_does_not_promote_reply_or_evidence() -> None:
    text = read(SENT)
    for marker in (
        "providerVerifiedSent = true",
        "sendProvider = \"Gmail sent mailbox\"",
        "sentLocalTimestamp = \"2026-10-16T12:30:17+10:00\"",
        "tobias.bothwell@colorado.edu",
        "ye@jila.colorado.edu",
        "authorRequestSent = true",
        "authorReplyReceived = false",
        "sendReceiptIsExperimentalEvidence = false",
        "rawExperimentArraysAcquired = false",
        "analysisCodeAcquired = false",
    ):
        assert marker in text


def test_packet_does_not_re_request_already_paid_public_coordinates() -> None:
    text = read(MODULE)
    for marker in (
        "sourceArtifactIdentityAlreadyPaid = true",
        "sourceAccessDateAlreadyPaid = true",
        "gravitationalPotentialModelAlreadyPaid = true",
        "publishedSystematicsSummaryAlreadyPaid = true",
    ):
        assert marker in text


def test_status_and_rollup_expose_sent_acquisition_without_promotion() -> None:
    status = read(STATUS)
    for marker in (
        "externalAcquisitionPacketConstructed = true",
        "externalAuthorRequestSent = true",
        "externalAuthorReplyReceived = false",
        "genericAcceptanceTokenConstructed = false",
        "terminalSIMetrologyPromotionAllowed = false",
    ):
        assert marker in status

    rollup = read(ROLLUP)
    for line in (
        "import DASHI.Physics.Closure.BothwellYe2022ExternalAcquisitionMaxCut",
        "import DASHI.Physics.Closure.BothwellYe2022AuthorCorrespondenceReceiptExact",
    ):
        assert rollup.count(line) == 1
