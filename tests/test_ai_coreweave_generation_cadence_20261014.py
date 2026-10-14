from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def test_coreweave_generation_cadence_surface():
    p = ROOT / "DASHI/Economics/AICoreWeaveGPUGenerationCadence20261014Exact.agda"
    text = p.read_text(encoding="utf-8")
    for marker in [
        "coreWeaveSelectedFrontierCadence",
        "selectedMaxTransitionMonthsIs17",
        "selectedMeanTransitionTenthsMonthsIs105",
        "frontierCadenceShorterThanBookLife",
        "generationCadenceDoesNotDetermineRetirementCadence",
    ]:
        assert marker in text
