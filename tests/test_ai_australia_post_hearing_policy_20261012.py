from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def require(path: str, markers: list[str]) -> None:
    text = (ROOT / path).read_text(encoding="utf-8")
    for marker in markers:
        assert marker in text, f"missing {marker!r} in {path}"


def test_post_hearing_policy_boundary() -> None:
    require(
        "DASHI/Economics/AIAustraliaPostHearingPolicy20261012Exact.agda",
        [
            "mandatoryGuardrailsNotProceedingAtThisTime",
            "openAIApologyAndMonitoringResponseObserved",
            "seriousIncidentReportingProposalObserved",
            "incidentResponseChronologyPaid",
            "realisedComplianceCostStillOpen",
            "concentrationCausalEffectStillOpen",
            "policyResponseDoesNotCreateRegulatoryCapture",
        ],
    )
