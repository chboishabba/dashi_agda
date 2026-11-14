from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def require(path: str, markers: list[str]) -> None:
    text = (ROOT / path).read_text(encoding="utf-8")
    for marker in markers:
        assert marker in text, f"missing {marker!r} in {path}"


def test_parliamentary_evidence_temporal_firewall() -> None:
    require(
        "DASHI/Law/OpenAIMedicareParliamentaryEvidence20261006Exact.agda",
        [
            "openAIParliamentaryResponseEvidence",
            "postIncidentMonitoringEstablished",
            "delayedNotificationAcknowledged",
            "preIncidentKnowledgeNotEstablished",
            "remedialMeasuresDoNotAutoProvePriorFault",
            "postIncidentKnowledgeDoesNotAutoProveJuneMensRea",
        ],
    )


def test_sensiblaw_rollup_imports_hearing_evidence() -> None:
    require(
        "DASHI/Law/SensibLawITIRParityEverything.agda",
        ["OpenAIMedicareParliamentaryEvidence20261006Exact"],
    )
