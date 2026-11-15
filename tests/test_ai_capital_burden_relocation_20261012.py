from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def require(path: str, markers: list[str]) -> None:
    text = (ROOT / path).read_text(encoding="utf-8")
    for marker in markers:
        assert marker in text, f"missing {marker!r} in {path}"


def test_capital_burden_relocation_surface() -> None:
    require(
        "DASHI/Economics/AICapitalBurdenRelocation20261012Exact.agda",
        [
            "oracleCustomerFundedScaleIs75",
            "illustrativeBeforeSystemBurdenIs75",
            "illustrativeAfterSystemBurdenIs75",
            "customerFundingDoesNotEraseSystemBurden",
            "sourceDoesNotIdentifyOracleCounterfactualBurden",
        ],
    )
