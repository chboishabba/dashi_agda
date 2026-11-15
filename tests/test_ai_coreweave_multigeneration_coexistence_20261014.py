from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def test_multigeneration_coexistence_surface():
    text = (ROOT / "DASHI/Economics/AICoreWeaveMultiGenerationCommercialCoexistence20261014Exact.agda").read_text(encoding="utf-8")
    for marker in [
        "coreWeaveCurrentCommercialCoexistence",
        "a100StillOffered",
        "h100StillOffered",
        "h200StillOffered",
        "rubinProductionPaid",
        "successorDoesNotImplyPriorGenerationCommercialExit",
    ]:
        assert marker in text
