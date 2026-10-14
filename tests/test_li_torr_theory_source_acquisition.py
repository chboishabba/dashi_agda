from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MODULE = ROOT / "DASHI/Physics/ExoticGravity/LiTorrTheorySourceAcquisitionExact.agda"


def text() -> str:
    assert MODULE.is_file(), f"missing {MODULE}"
    return MODULE.read_text(encoding="utf-8", errors="replace")


def test_primary_and_inspection_roles_remain_distinct():
    s = text()
    for needle in (
        "liTorrPRD1991PrimaryAPS",
        "liTorrPRB1992PrimaryAPS",
        "liTorrPRB1992InspectedReproduction",
        "kowitt1994PrimaryAPS",
        "reproductionCreatesPublicationAuthority = false",
        "citationImportsScientificProof = false",
    ):
        assert needle in s


def test_1991_and_1992_bounded_claims_have_exact_locators():
    s = text()
    for needle in (
        "prd1991AttenuationAcquired",
        "APS abstract",
        "prb1992CoupledResponseAcquired",
        "Phys. Rev. B 46, 5492",
        "Eqs. (33)-(35)",
        "A(k,omega) + (m/q) A_g(k,omega)",
    ):
        assert needle in s


def test_1993_full_carrier_remains_open_and_critique_is_not_theory_identity():
    s = text()
    for needle in (
        "fopl1993MicroscopicCarrierStillOpen = true",
        "kowittCritiqueDoesNotRewriteLiTorrSource = true",
        "historicalEquationShapeEstablishedPhysics = false",
    ):
        assert needle in s
