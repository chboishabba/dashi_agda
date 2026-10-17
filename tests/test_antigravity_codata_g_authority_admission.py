from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def read(rel: str) -> str:
    path = ROOT / rel
    assert path.is_file(), f"missing {rel}"
    return path.read_text(encoding="utf-8", errors="replace")


def test_codata_g_source_is_attributed_but_non_promoting():
    text = read(
        "DASHI/Physics/ExoticGravity/"
        "AntigravityCODATA2022GAuthorityAdmissionExact.agda"
    )
    for token in (
        "nistCODATA2022DatabaseSource",
        "Source.mkNoDOISource",
        "citationCreatesAuthority",
        "sourceAtlasDoesNotCreateAuthority",
        "sourceEntitlesCurrent2022CODATAStatus",
        "sourceEntitlesGValueAndStandardUncertainty",
    ):
        assert token in text


def test_g_authority_admission_binds_exact_value_uncertainty_and_dimension():
    text = read(
        "DASHI/Physics/ExoticGravity/"
        "AntigravityCODATA2022GAuthorityAdmissionExact.agda"
    )
    for token in (
        "gValueSI",
        "gStandardUncertaintySI",
        "gLowerSI",
        "gUpperSI",
        "Payload.newtonianGDimensionVector",
        "AntigravityGAuthorityAdmission",
        "canonicalAntigravityGAuthorityAdmission",
        "acceptedMeasuredGAuthorityPaid",
        "acceptedMeasuredGAuthorityStillRequired",
    ):
        assert token in text


def test_si_frontier_consumes_admitted_g_authority_without_claiming_exact_g():
    text = read(
        "DASHI/Physics/ExoticGravity/AntigravitySICalibrationDonorMaxCutExact.agda"
    )
    assert "AntigravityCODATA2022GAuthorityAdmissionExact" in text
    assert "acceptedMeasuredGAuthorityStillRequired =" in text
    assert "GAuthority.acceptedMeasuredGAuthorityStillRequired" in text
    assert "exactNewtonianGClaimed" in text
