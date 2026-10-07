from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def read(rel: str) -> str:
    p = ROOT / rel
    assert p.is_file(), f"missing {rel}"
    return p.read_text(encoding="utf-8", errors="replace")


def test_cmp119_nambu_readout_reuses_existing_localized_action_projector():
    text = read("DASHI/Physics/Foundations/GRQFTCMP119NambuBuriedVacuumReadoutExact.agda")
    for token in (
        "localizedVacuumReadout",
        "plaquetteCoefficientProjector",
        "sourceVacuumAmplitudeAt",
        "readoutCarrierAlreadyExists",
        "twoSelectedSourceValuesStillNeedProof",
    ):
        assert token in text


def test_terminal_no_longer_calls_the_readout_carrier_missing():
    text = read("DASHI/Physics/ExoticGravity/AntigravityABCDETerminalMaxCutExact.agda")
    assert "sourceNativeVacuumReadoutCarrierConstructed" in text
    assert "sourceNativeTwoVacuumValuesStillOpen" in text
