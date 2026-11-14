from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def require(path: str, markers: list[str]) -> None:
    text = (ROOT / path).read_text(encoding="utf-8")
    for marker in markers:
        assert marker in text, f"missing {marker!r} in {path}"


def test_named_payer_saturation_surface() -> None:
    require(
        "DASHI/Economics/AICoreWeaveNamedPayerSaturation20261012Exact.agda",
        [
            "microsoftExternalCashEdgePaid",
            "metaExternalCashEdgePaid",
            "openAIContractEdgePaidCashProvenanceOpen",
            "anonymousCurrentTopCustomerIdentityStillOpen",
            "twoNamedExternalCashEdgesDoNotCloseWholeGraph",
        ],
    )


def test_rollup_imports_named_payer_saturation() -> None:
    require(
        "DASHI/Economics/AIEntanglementEverything2026.agda",
        ["AICoreWeaveNamedPayerSaturation20261012Exact"],
    )
