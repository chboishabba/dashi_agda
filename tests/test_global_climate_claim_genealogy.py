"""Source-root regression for WORLDWIDE global-cooling / CO2-plant-food claims.

This verifies audited document roles and nonpromotion. It does not verify
all historical film credits/financing, perform a random global sample, measure
plant physiology, establish intent or substitute for Agda kernel typechecking.
"""
from pathlib import Path
import csv

from scripts.global_climate_claim_genealogy_audit import (
    audit, read_ledger, CLAIM_FAMILIES, EDGES, UNPAID_TRANSMISSIONS
)

ROOT = Path(__file__).resolve().parents[1]
OWNER = ROOT / "DASHI/Governance/ClimateGenealogyTypedCasesExact.agda"
TYPED = ROOT / "DASHI/Governance/TypedGenealogyEdgeExact.agda"
REG = ROOT / "DASHI/Governance/EmpiricalGenealogyRound3Regression.agda"
GLOBAL_ROADMAP = ROOT / "Docs/roadmaps/GlobalClimateDenialClaimGenealogy20261027.md"
ORIGINAL = ROOT / "Docs/support/reference/global_climate_denial_claim_genealogy_20261027.csv"


def test_global_cooling_plant_claims_source_schema_and_scoped_origins():
    rows = read_ledger()
    by = {r["record_id"]: r for r in rows}
    assert len(rows) == len(by) == 18
    assert len({r["source_object_id"] for r in rows}) == 18
    assert {r["claim_family"] for r in rows} == CLAIM_FAMILIES
    assert by["GC01"]["source_date"] == "1975-04-28"
    assert "Peter Gwynne" in by["GC01"]["original_author_or_institution"]
    assert by["GC01"]["source_object_id"] != by["GC02"]["source_object_id"]
    assert by["GC02"]["argument_root_family"] == by["GC01"]["argument_root_family"]
    assert by["GC03"]["argument_root_family"] != by["GC01"]["argument_root_family"]
    assert "7 cooling 20 neutral 44 warming" in by["GC03"]["attribution_and_nonpromotion_boundary"]
    assert by["GC04"]["argument_root_family"] != by["GC01"]["argument_root_family"]
    assert "2024" in by["GC06"]["attribution_and_nonpromotion_boundary"]
    assert "not a scientific literature census" in by["GC01"]["attribution_and_nonpromotion_boundary"]


def test_co2_plant_original_producer_and_nas_not_pnas():
    rows = read_ledger()
    by = {r["record_id"]: r for r in rows}
    assert "Western Fuels Association" in by["GP01"]["original_author_or_institution"]
    assert by["GP01"]["source_role"] == "archive_index_original_film_unviewed"
    assert by["GP02"]["argument_root_family"] == by["GP01"]["argument_root_family"]
    assert by["GP02"]["relation_to_previous"] == "named_sequel_same_campaign_root"
    assert by["GP03"]["argument_root_family"] != by["GP01"]["argument_root_family"]
    assert "31000" in by["GP03"]["attribution_and_nonpromotion_boundary"]
    assert "self-report" in by["GP03"]["attribution_and_nonpromotion_boundary"]
    assert "Sallie" in by["GP04"]["original_author_or_institution"]
    assert "1998" in by["GP04"]["source_date"]
    assert by["GP04"]["argument_root_family"] == by["GP06"]["argument_root_family"]
    assert by["GP04"]["source_object_id"] != by["GP06"]["source_object_id"]
    assert by["GP05"]["source_locator"].startswith("https://www.nationalacademies.org/")
    assert "was not then" in by["GP05"]["attribution_and_nonpromotion_boundary"] or \
           "at that time" in by["GP05"]["attribution_and_nonpromotion_boundary"]
    assert "Undated" not in by["GP07"]["source_date"] or \
           by["GP07"]["source_date"].startswith("undated")
    assert by["GP07"]["independent_empirical_origin"] == "not_an_independent_plant_experiment"
    assert "2016" in by["GP09"]["source_date"]
    assert "70%" in by["GP09"]["attribution_and_nonpromotion_boundary"]
    assert "nutrient constraints" in by["GP11"]["attribution_and_nonpromotion_boundary"]


def test_global_source_audit_does_not_generate_fake_world_denominator():
    report = audit(read_ledger())
    assert report["selected_appearances"] == 18
    assert len(report["selected_claim_families"]) == 8
    assert report["source_objects"] == 18
    assert report["global_population_estimate"] is None
    assert len(report["documented_scoped_relations"]) == len(EDGES) == 4
    assert len(report["unproved_relevant_transmissions"]) == len(UNPAID_TRANSMISSIONS) == 4
    assert any(e["type"] == "original-author-self-correction"
               for e in report["documented_scoped_relations"])
    assert any(e["type"] == "explicit-institutional-disavowal"
               for e in report["documented_scoped_relations"])
    assert any(e["from"] == "GP01" and e["to"] == "GP07"
               for e in report["unproved_relevant_transmissions"])
    assert "not a global representative sample" in report["warning"]
    assert report["argument_family_inventory_not_independent_sources"]


def test_negative_mutations_fail_closed():
    rows = read_ledger()
    changed = [dict(r) for r in rows]
    by = {r["record_id"]: r for r in changed}
    by["GP07"]["source_date"] = "2015-01-01"  # artificial retro-dating
    try:
        audit(changed)
    except ValueError as exc:
        assert "Undated CO2 Coalition webpage" in str(exc)
    else:
        raise AssertionError("False publisher history accepted")

    changed = [dict(r) for r in rows]
    by = {r["record_id"]: r for r in changed}
    by["GP03"]["argument_root_family"] = by["GP01"]["argument_root_family"]
    try:
        audit(changed)
    except ValueError as exc:
        assert "OISM merged" in str(exc)
    else:
        raise AssertionError("Unproved WFA-to-OISM origin copied")

    changed = [dict(r) for r in rows]
    by = {r["record_id"]: r for r in changed}
    by["GC04"]["argument_root_family"] = by["GC01"]["argument_root_family"]
    try:
        audit(changed)
    except ValueError as exc:
        assert "1975 cooling media and 1998-window" in str(exc)
    else:
        raise AssertionError("Two different cooling claims conflated")


def test_global_agda_reuses_canonical_relations_and_finite_barriers():
    owner = OWNER.read_text()
    typed = TYPED.read_text()
    reg = REG.read_text()
    docs = GLOBAL_ROADMAP.read_text()
    for relation in ("authorRetrospectiveCorrection",
                     "institutionalDisavowal", "extrapolationBeyondEvidence"):
        assert relation + " : RelationKind" in typed
    for source in ("globalCoolingGwynneOriginal1975", "globalCoolingGwynneRetrospective2014",
                   "globalGreeningWFAFilmIndex1992", "globalNAS1998PetitionDisavowal",
                   "globalZhuOriginalGreening2016", "globalTerrerFertilisationLimit2016",
                   "globalOISMOriginalManuscript1998", "globalWFA1998NamedFilmContributorsIndex"):
        assert source + " : Typed.SourceReceipt" in owner
    for edge in ("globalGwynne1975To2014AuthorCorrection", "globalWFAToGreeningEarthSequel",
                 "globalNASDisavowsOISMPetition", "globalPlantGrowthIsNotNetClimateBenefit",
                 "globalSeitzPBSRoleToOISMPetition", "globalBaliunasTwoDocumentFamilies"):
        assert edge + " : Typed.TypedGenealogyEdge" in owner
    assert "samePlantGrowthDifferentGlobalNetAssessment" in owner
    assert "sameNewsweekArticleDifferentScientificField" in owner
    assert "positivePlantResponseDoesNotIdentifyGlobalNetImpact" in owner
    assert "oneCoolingMagazineArticleCannotDetermineScientificConsensus" in owner
    assert "globalPositiveFertilisationIsNotNetClimateHarmEvaluation" in reg
    assert "global1975MediaArticleIsNotContemporaryScienceCensus" in reg
    assert "globalNAS1998OriginalInstitutionDisavowal" in reg
    assert "globalSeitzSamePersonNoPaymentBridge" in reg
    assert "globalBaliunasNamedOverlapNoScriptProof" in reg
    assert "WORLDWIDE" in docs or "worldwide" in docs
    assert "Australia/BOM/gas-tax cases are a **separate local comparison**" in docs
    assert "global" in docs.lower()
    assert "not a global" in docs.lower()
