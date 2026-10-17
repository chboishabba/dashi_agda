from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CLOSURE = ROOT / "DASHI" / "Physics" / "Closure"

TRANSPORT = CLOSURE / "ZhengKolkowitz2023TransportAttemptReceiptExact.agda"
DEBT = CLOSURE / "QuantumClockEmpiricalDebtRouting20261017Exact.agda"
STATUS = CLOSURE / "QuantumClockEmpiricalRedshiftIngestionStatus20261017Exact.agda"
ROLLUP = CLOSURE / "YeRedshiftEverything.agda"


def read(path: Path) -> str:
    assert path.is_file(), f"missing {path.relative_to(ROOT)}"
    return path.read_text(encoding="utf-8")


def test_zenodo_transport_attempt_keeps_manifest_transport_and_payload_distinct() -> None:
    text = read(TRANSPORT)
    for marker in (
        "10.5281/zenodo.8184043",
        "manifestResolved = true",
        "payloadTransportSucceeded = false",
        "payloadBytesMaterialised = false",
        "payloadDigestVerified = false",
        "transportAttemptEstablishesEmpiricalResult = false",
        "transportFailureInvalidatesSourceManifest = false",
        "web file links returned cache-miss / HTTP 429 and container download failed",
    ):
        assert marker in text


def test_clock_frontier_reuses_canonical_proof_debt_router() -> None:
    text = read(DEBT)
    for marker in (
        "import DASHI.Core.ProofDebtRouterExact as Debt",
        "Bothwell/Ye author-supplied raw arrays and analysis replay",
        "Zheng/Kolkowitz public process-data byte materialisation and replay",
        "Debt.empiricalEvidenceDebt",
        "Debt.verifyEmpiricalEvidence",
        "bothwellEvidenceIsNotMathematicalDebt = true",
        "zhengReplayIsNotMathematicalDebt = true",
        "kernelCertificationIsSeparateDebt = true",
    ):
        assert marker in text


def test_oct17_status_advances_events_without_rewriting_oct16_snapshot() -> None:
    text = read(STATUS)
    for marker in (
        "priorStatus20261016",
        "authorReplyReceived = false",
        "zenodoManifestResolved = true",
        "zenodoPayloadTransportSucceeded = false",
        "bothwellEvidenceDebtRouted = true",
        "zhengEvidenceDebtRouted = true",
        "terminalEmpiricalPromotionAllowed = false",
    ):
        assert marker in text

    rollup = read(ROLLUP)
    for line in (
        "import DASHI.Physics.Closure.ZhengKolkowitz2023TransportAttemptReceiptExact",
        "import DASHI.Physics.Closure.QuantumClockEmpiricalDebtRouting20261017Exact",
        "import DASHI.Physics.Closure.QuantumClockEmpiricalRedshiftIngestionStatus20261017Exact",
    ):
        assert rollup.count(line) == 1
