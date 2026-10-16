from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def test_phase_roadmap_promotes_same_object_financing_not_generic_life_gap():
    text = (ROOT / "DASHI/Economics/AICapitalPhaseRoadmap20261016Exact.agda").read_text(encoding="utf-8")
    for marker in [
        "sameObjectFinancingMaxCutPaid",
        "contractRealisationCureNonDescentPaid",
        "sameInstrumentBondRepricingPaid",
        "historicalNamedMicrosoftRevenuePaid",
        "generic36To48MonthClockNotSameObject",
        "realisedRefinancingStillOpen",
    ]:
        assert marker in text
