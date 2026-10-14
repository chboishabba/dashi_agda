from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def test_capacity_vintage_non_descent_owner():
    p = ROOT / "DASHI/Economics/AICoreWeaveCapacityHardwareAgeNonDescent20261014Exact.agda"
    text = p.read_text(encoding="utf-8")
    for marker in [
        "sameCapacityDifferentHardwareAgeWitness",
        "capacityVintageCannotFactorHardwareAge",
        "refreshCoordinateSeparatesWitness",
        "capacityAgeDoesNotDetermineHardwareAge",
    ]:
        assert marker in text
