"""Static source-boundary regression for 2026-10 BOM/Fordham case.

This guards source/claim classifications, not climate-data computations, speaker
intent, the original Berger/Sherrington audit, or Agda kernel typechecking.
"""
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OWNER = ROOT / "DASHI/Governance/BOMFordhamMediaClaimAuditExact.agda"
VALIDATION = ROOT / "DASHI/Governance/BOMFordhamMediaClaimAuditValidation.agda"
RESEARCH = ROOT / "docs/bom_fordham_temperature_claim_audit_20261024.md"


def test_existing_typed_genealogy_reused():
    text = OWNER.read_text()
    assert "import DASHI.Governance.TypedGenealogyEdgeExact as Typed" in text
    for edge, kind in [
        ("fordhamTo2GB", "Typed.personnelContinuity"),
        ("radioToTapt", "Typed.organisationalContinuity"),
        ("fordhamAuditBroadcast", "Typed.audienceAdjacency"),
    ]:
        assert edge in text and kind in text
    # No candidate is installed as a strong transfer evidence edge.
    assert "Typed.historicalTransfer Typed.primary" not in text
    assert "Typed.directMethodTransfer Typed.primary" not in text


def test_source_roots_preserve_chronology_and_not_obtained_audit():
    text = OWNER.read_text()
    assert "2026-10-19 AEST" in text
    assert "2026-10-22" in text
    assert "2026-05-01" in text
    assert "canonicalOriginalAuditStatus = notAcquired" in text
    assert "institutionHypothesised bomStatement" in text
    assert "allegationNotReproduced auditReporting" in text


def test_nonpromotion_regressions_and_bondi_distinction():
    code = OWNER.read_text()
    val = VALIDATION.read_text()
    docs = RESEARCH.read_text()
    required = [
        "duplicateDoesNotProveFraud",
        "rhetoricDoesNotProveBannonControl",
        "ownershipDoesNotProveEditorialOrder",
        "bondiCoverageDoesNotProveInflammatorySpeech",
        "fordhamTPUSA", "fordhamTPAU", "fordhamBannon",
    ]
    for name in required:
        assert name in code
    assert "noFraudPromotion" in val
    assert "noTPUSAPromotion" in val
    assert "2024 Bondi Junction" in docs
    assert "2025 Bondi Beach" in docs
    assert "1867 is pre-1910" in docs
    assert "postdates the episode" in docs


def test_bondi_media_and_false_hanson_attribution_are_separate_roots():
    owner = OWNER.read_text()
    docs = RESEARCH.read_text()
    for name in [
        "bondiFordhamPoliticalSegment",
        "fordhamLathamArchive",
        "aapBondiHansonFabrication",
        "tpaustFirstParty",
    ]:
        assert name in owner
    assert "fabricated quotes attributed to Pauline Hanson" in docs
    assert "not anti-Muslim words" in docs
    assert "Latham" in docs and "underlying allegation" not in owner


POLITICAL_OWNER = ROOT / "DASHI/Governance/AustralianPoliticalRadioInfluence2026Exact.agda"
POLITICAL_VALIDATION = ROOT / "DASHI/Governance/AustralianPoliticalRadioInfluence2026Validation.agda"


def test_direct_2026_ownership_and_revenue_do_not_collapse():
    body = POLITICAL_OWNER.read_text()
    docs = RESEARCH.read_text()
    for required in (
        "fordhamTapt",
        "kiisARN",
        "arnSandilandsRevenue",
        "arnNewsCorpExit",
        "19.9 percent",
        "ceased to be substantial holder",
        "2026-05-01",
    ):
        assert required in body or required in docs
    assert "noRevenueControlLeap" in body


def test_first_person_messaging_and_disputed_work_status():
    body = POLITICAL_OWNER.read_text()
    val = POLITICAL_VALIDATION.read_text()
    assert "kyleHansonMessaging" in body
    assert "namedActorSelfReport" in body
    assert "ashbyKyleQualification" in body
    assert "namedActorDenial" in body
    assert "noPaidCampaignPromotion" in val


def test_funding_event_attendance_and_climate_are_typed_distinct():
    body = POLITICAL_OWNER.read_text()
    for term in (
        "hancockAdvance",
        "advanceBannonAssociate",
        "harnwellBannon",
        "rinehartHansonPolicy",
        "plimerOneNation",
        "palmerBannonConflict",
        "acmaMpoxFinding",
        "acmaParalympicsFinding",
        "noFordhamCommandLeap",
    ):
        assert term in body
    assert "noPalmerClaimPromotion" in body
    assert "noConferenceCommand" in POLITICAL_VALIDATION.read_text()
