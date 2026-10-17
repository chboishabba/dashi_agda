from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def read(rel: str) -> str:
    path = ROOT / rel
    assert path.is_file(), f"missing {rel}"
    return path.read_text(encoding="utf-8", errors="replace")


def test_tt_route_is_reduced_to_literal_same_object_welds():
    text = read("DASHI/Physics/ExoticGravity/AntigravityDifferentialTTDonorMaxCutExact.agda")
    for token in (
        "newMaxwellTheoryRequired",
        "newMetricDependentHodgeTheoryRequired",
        "newR144FirstVariationFrameworkRequired",
        "canonicalMetricStressPairingTheoremAlreadyOwned",
        "sameGWMetricTangentStillRequired",
        "sameEMHilbertStressInsertionStillRequired",
        "sameFirstVariationPairingStillRequired",
        "sameFirstVariationPairingFollowsAfterMetricDomainAndStressIdentification",
        "sameLocalizedInteractionStillRequired",
        "scalarKottlerDeltaGttAloneConstructsTTMode",
        "schutzhold1099IsDonorNotImportedAuthority",
    ):
        assert token in text
    assert "sameFirstVariationPairingStillRequired = false" in text
    assert "sameFirstVariationPairingFollowsAfterMetricDomainAndStressIdentification = true" in text
