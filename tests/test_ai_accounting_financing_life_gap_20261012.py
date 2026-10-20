from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def require(path: str, markers: list[str]) -> None:
    text = (ROOT / path).read_text(encoding="utf-8")
    for marker in markers:
        assert marker in text, f"missing {marker!r} in {path}"


def test_accounting_financing_life_gap_surface() -> None:
    require(
        "DASHI/Economics/AIAccountingFinancingLifeGap20261012Exact.agda",
        [
            "coreWeaveAccountingLifeMonthsIs72",
            "lenderHorizonLowerMonthsIs36",
            "lenderHorizonUpperMonthsIs48",
            "selectedGapLowerMonthsIs24",
            "selectedGapUpperMonthsIs36",
            "lifeGapIsObsolescencePressureEvidence",
            "genericLenderHorizonDoesNotDetermineCoreWeaveEconomicLife",
        ],
    )
