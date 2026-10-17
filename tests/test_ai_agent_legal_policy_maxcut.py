from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def require(path: str, markers: list[str]) -> None:
    text = (ROOT / path).read_text(encoding="utf-8")
    for marker in markers:
        assert marker in text, f"missing {marker!r} in {path}"


def test_commonwealth_agent_offence_attribution_surface() -> None:
    require(
        "DASHI/Law/AustralianCommonwealthAgentComputerOffenceAttribution2026Exact.agda",
        [
            "section4781",
            "restrictedDataControlSystemRequired",
            "corporatePhysicalAttributionRoute",
            "corporateFaultAttributionRoute",
            "softwareAgentDoesNotAutoBecomeStatutoryAgent",
            "medicare4781ApplicationBoundary",
        ],
    )


def test_legal_acquisition_progress_surface() -> None:
    require(
        "DASHI/Law/AIAgentLegalAcquisitionProgress20261012Exact.agda",
        [
            "candidateOffenceSourceAcquired",
            "applicabilityStillOpen",
            "runtimeTraceStillOpen",
            "corporateFaultStillOpen",
            "financialAgentReuseStillSourceConditioned",
        ],
    )


def test_rollups_import_new_surfaces() -> None:
    require(
        "DASHI/Law/SensibLawITIRParityEverything.agda",
        [
            "AustralianCommonwealthAgentComputerOffenceAttribution2026Exact",
            "AIAgentLegalAcquisitionProgress20261012Exact",
        ],
    )
