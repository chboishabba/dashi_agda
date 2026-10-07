from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def read(rel: str) -> str:
    p = ROOT / rel
    assert p.is_file(), f"missing {rel}"
    return p.read_text(encoding="utf-8", errors="replace")


def test_nambu_kottler_observable_compiler_is_concrete():
    text = read("DASHI/Physics/ExoticGravity/AntigravityNambuKottlerObservableCompilerExact.agda")
    for token in (
        "fixtureOutwardFreeFall",
        "fixtureSupportWeightChange",
        "fixtureExteriorLapseRoot",
        "fixtureInteriorLapseRoot",
        "kottlerLapseDeltaLinear",
        "fixtureMetricTTDeltaIsFourThirdsDeltaLambda",
        "sameNambuKottlerGeometryFeedsMechanicalAndClockChannels",
        "SchutzholdTTModeIdentificationStillOpen",
    ):
        assert token in text


def test_terminal_consumes_concrete_nambu_kottler_observables():
    text = read("DASHI/Physics/ExoticGravity/AntigravityABCDETerminalMaxCutExact.agda")
    for token in (
        "stageDConcreteNambuKottlerObservables",
        "stageDKottlerAmplitudeToMetricPerturbationClosed",
        "physicalAmplitudeModulationStillOpen",
        "schutzholdTTModeSameObjectStillOpen",
    ):
        assert token in text
