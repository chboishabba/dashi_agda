"""Static/source-bound regression for the Aquino/Maxwell/Epstein/CA case delta.

These checks do NOT certify Agda, the source documents, or historical truth.
The Agda kernel command is tracked separately in the roadmap.
"""
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OWNER = ROOT / "DASHI/Cognition/AquinoMaxwellEpsteinCAMaxCutExact.agda"
ROLLUP = ROOT / "DASHI/Cognition/Everything.agda"
ROADMAP = ROOT / "docs/research/aquino-maxwell-epstein-ca-maxcut-20261024.md"


def test_existing_prior_art_reused_not_cloned():
    text = OWNER.read_text()
    assert "import DASHI.Cognition.BannonCambridgeAnalyticaInfluenceInfrastructureExact as CA" in text
    assert "import DASHI.Cognition.EpsteinMasterPlanAttributionBoundaryExact as Plan" in text
    assert "import DASHI.Governance.EvidenceGradedGenealogyCore as Genealogy" in text
    assert "module DASHI.Cognition.AquinoMaxwellEpsteinCAMaxCutExact where" in text
    assert "import DASHI.Cognition.AquinoMaxwellEpsteinCAMaxCutExact" in ROLLUP.read_text()


def test_source_roots_roles_and_contradictions_are_retained():
    text = OWNER.read_text()
    for fragment in (
        "wylieRoot", "aquinoVallelyRoot", "fourthCircuitRoot",
        "ftcRoot", "houseJudiciaryRoot", "buaDOJRoot",
        "dojFBIMemoRoot", "epsteinCorrespondenceRoot",
        "judicialProceduralDecision", "regulatoryFinding",
        "attributedFirstPersonTestimony", "disputedAgencyReview",
        "1992-02-26", "2025-07",
    ):
        assert fragment in text
    assert "The House hearing and Wylie's submitted statement" in ROADMAP.read_text()


def test_attribution_firewalls_and_same_object_checks():
    text = OWNER.read_text()
    for fragment in (
        "robertMaxwellIsNotRobertMercer ()",
        "mindWarIsNotStargate ()",
        "aquinoToSCLUnpaid = refl",
        "aquinoToEpsteinUnpaid = refl",
        "promisMaxwellUnpaid = refl",
        "unifiedHierarchyUnpaid = refl",
        "existingCAMediaReuseUnpaid = refl",
        "existingMasterPlanHierarchyUnpaid = refl",
        "existingGenealogyDoesNotPromoteAnalogy = refl",
        "noWitnessMultiplication ()",
        "noTechniquePromotion ()",
        "noGuiltByAllegation ()",
        "noUnifiedCommandFromNetworkPath ()",
    ):
        assert fragment in text


def test_source_locator_or_attributed_local_owner():
    text = OWNER.read_text()
    assert "https://committees.parliament.uk/writtenevidence/89475/html/" in text
    assert "https://law.justia.com/cases/federal/appellate-courts/F2/957/139/2044/" in text
    assert "https://www.justice.gov/opa/media/1407001/dl" in text
    assert "TrumpMarALagoBannonBridgeExact" in text
    assert ROADMAP.exists()
