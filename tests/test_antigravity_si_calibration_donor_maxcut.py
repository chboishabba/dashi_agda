from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def read(rel: str) -> str:
    path = ROOT / rel
    assert path.is_file(), f"missing {rel}"
    return path.read_text(encoding="utf-8", errors="replace")


def test_si_calibration_is_reduced_to_authority_and_stress_length_product():
    text = read("DASHI/Physics/ExoticGravity/AntigravitySICalibrationDonorMaxCutExact.agda")
    for token in (
        "vendoredCODATAEinsteinCouplingCandidateAvailable",
        "exactSpeedOfLightIsNotCalibrationBlocker",
        "acceptedMeasuredGAuthorityStillRequired",
        "sourceStressLengthSquaredScaleStillRequired",
        "separateStressAndLengthIdentificationRequired",
        "newEinsteinCouplingConventionRequired",
    ):
        assert token in text
