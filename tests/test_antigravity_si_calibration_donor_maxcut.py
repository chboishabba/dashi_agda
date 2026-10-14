from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def read(rel: str) -> str:
    path = ROOT / rel
    assert path.is_file(), f"missing {rel}"
    return path.read_text(encoding="utf-8", errors="replace")


def test_si_calibration_is_reduced_to_one_source_scale_payment():
    text = read("DASHI/Physics/ExoticGravity/AntigravitySICalibrationDonorMaxCutExact.agda")
    required = (
        "vendoredCODATAEinsteinCouplingCandidateAvailable",
        "exactSpeedOfLightIsNotCalibrationBlocker",
        "acceptedMeasuredGAuthorityPaid = true",
        "acceptedMeasuredGAuthorityStillRequired = false",
        "acceptedPhysicalEinsteinCouplingAvailable = true",
        "sourceStressLengthSquaredScaleStillRequired = true",
        "separateStressAndLengthIdentificationRequired = false",
        "newEinsteinCouplingConventionRequired = false",
        "remainingSICalibrationPhysicalPackageCount = 1",
    )
    for token in required:
        assert token in text
