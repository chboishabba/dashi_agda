from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def test_openai_contract_realisation_cure_does_not_become_customer_cash():
    text = (ROOT / "DASHI/Economics/AICoreWeaveOpenAIContractRealisationCure20261016Exact.agda").read_text(encoding="utf-8")
    for marker in [
        "contractRealisationFloorBpIs8500",
        "testingPostponedTo20260228",
        "unlimitedEquityCuresThrough20261027Paid",
        "equityCureCanRepairCovenantMetric",
        "equityCureDoesNotCreateOpenAICustomerCash",
        "realisedContractRatioStillPrivate",
    ]:
        assert marker in text
