from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def require(path: str, markers: list[str]) -> None:
    text = (ROOT / path).read_text(encoding="utf-8")
    for marker in markers:
        assert marker in text, f"missing {marker!r} in {path}"


def test_australia_policy_acquisition_surface() -> None:
    require(
        "DASHI/Economics/AIAustraliaRegulatoryPolicyAcquisition20261012Exact.agda",
        [
            "mandatoryGuardrailsProposalAcquired",
            "mandatoryGuardrailsCurrentlyProceeding",
            "regulatoryImpactSurveyAcquired",
            "sameBasisCostVectorStillOpen",
            "voluntaryGuidanceDoesNotEqualMandatoryRule",
            "proposalWithdrawalDoesNotDisproveStructuralMoatMechanism",
        ],
    )


def test_rollups_import_policy_acquisition() -> None:
    require(
        "DASHI/Economics/AIEntanglementEverything2026.agda",
        ["AIAustraliaRegulatoryPolicyAcquisition20261012Exact"],
    )
