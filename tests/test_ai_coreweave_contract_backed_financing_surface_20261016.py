from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def test_contract_backed_financing_surface_is_source_bounded():
    text = (ROOT / "DASHI/Economics/AICoreWeaveContractBackedFinancingSurface20261016Exact.agda").read_text(encoding="utf-8")
    for marker in [
        "ddtl3SOFRMarginBpIs400",
        "ddtl4SOFRMarginBpIs225",
        "ddtl5SOFRMarginBpIs450",
        "ddtl55SOFRMarginBpIs550",
        "financingRateIsProjectSpecific",
        "oneCompanyWideRateNotPromotable",
    ]:
        assert marker in text
