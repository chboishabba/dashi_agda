#!/usr/bin/env python3
"""Fail-closed source-level GCC/Harrison + Exxon-180 research ledger.

No claims of changed media/policy outcomes without reviewed complete
outlet-level observations and independent comparison measurements.
Published PR self-reports and archive excerpts are source assertions.
"""
from __future__ import annotations

import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "Docs/research/ccdcoe_p3_gcc_executed_campaign_case.json"
AGDA = ROOT / "DASHI/Cognition/CCDCOEP3GCCExecutedCampaignSourceExact.agda"
GOLDEN = ROOT / "DASHI/Cognition/Everything.agda"
FOCUSED = ROOT / "scripts/check_ccdcoe_cognition_agda.sh"

def validate(data: dict, agda: str, golden: str, focused: str) -> dict:
    assert data["schema"] == "dashi.ccdcoe.p3.gcc_executed_case.v1"
    assert data["case_id"] == "gcc-ebruce-harrison-1993-1995"
    sources = {r["id"]: r for r in data["primary_sources"]}
    assert len(sources) == 5
    assert set(sources) == {
        "harrison_case_history", "gcc_1993_media_hits",
        "gcc_board_jul_11_1995", "brulle_2022", "frontline_2022"}
    for name, row in sources.items():
        assert row["url"].startswith("https://")
        assert row["original_pdf_sha256"] is None
        assert row["source_review_receipt"] is None
        assert row["source_type"] and row["title"]
    assert sources["harrison_case_history"]["original_date"] == "undated"
    assert sources["gcc_1993_media_hits"]["source_type"] == (
        "gcc_held_media_clipping_archive")
    assert sources["brulle_2022"]["doi"] == "10.1080/09644016.2022.2058815"

    claims = data["agency_claims"]
    assert {c["id"] for c in claims} == {
        "science_uncertainty_message", "economic_cost_message",
        "media_tours_and_editorial", "coverage_changed",
        "carbon_tax_debate", "voluntary_policy_influence"}
    assert all(c["source_id"] == "harrison_case_history" for c in claims)
    assert all(not c["independent_outcome_observed"] for c in claims)
    assert {c["kind"] for c in claims} == {
        "reported_intended_message", "agency_reported_delivery",
        "agency_self_assessed_effect"}
    assert all(c["source_text_line_range"][0] <=
               c["source_text_line_range"][1] for c in claims)
    assert sum(c["kind"] == "agency_self_assessed_effect" for c in claims) == 3

    media = data["media_observations"]
    assert len(media) == 2
    assert {e["id"] for e in media} == {
        "washington_post_satellite_vs_surface_1993",
        "nashville_banner_christy_1993"}
    assert {e["publication"] for e in media} == {
        "The Washington Post", "Nashville Banner"}
    assert all(e["source_id"] == "gcc_1993_media_hits" for e in media)
    assert all(e["year"] == 1993 for e in media)
    assert all(e["associated_with_gcc_archive"] for e in media)
    assert all(not e["gcc_direct_placement_identified"] for e in media)
    assert all(not e["original_article_fulltext_reviewed"] for e in media)
    assert all(not e["claim_text_coded"] for e in media)
    assert all(e["observed_frame"] is None and
               e["comparison_sample_receipt"] is None for e in media)
    assert data["archival_notice"]["source_id"] == "gcc_1993_media_hits"
    assert not data["archival_notice"]["bulletin_fulltext_reviewed"]

    flags = data["evidence_stage"]
    assert flags == {
        "strategy_reported_by_firm": True,
        "activity_delivery_reported_by_firm": True,
        "specific_media_clippings_located": True,
        "independent_historical_media_attention_measurements_located": True,
        "independent_media_prepost_change_measured": False,
        "outlet_level_sampling_frame_defined": False,
        "media_claim_codebook_applied": False,
        "causal_counterfactual_identified": False,
        "policy_impact_identified": False,
        "unknowns_must_remain_null": True,
    }
    design = data["planned_measurement"]
    assert "outlet" in design["unit"]
    assert design["estimand_status"] == "not_identified"
    assert design["confidence_intervals"] is None
    assert design["measured_outcome"] is None
    assert design["non_detection_not_zero_effect"] is True
    assert len(design["frame_categories"]) == 5
    assert "other_or_undetermined" in design["frame_categories"]
    assert "document acquisition bias" in design["required_covariates"]

    baseline = data["independent_media_baseline"]
    assert baseline["id"] == "trumbo_1996_five_newspaper_content_study"
    assert baseline["doi"] == "10.1088/0963-6625/5/3/006"
    assert baseline["outlet_scope"] == "five national US newspapers"
    assert baseline["document_type"] == "peer_reviewed_original_content_analysis"
    assert baseline["original_article_fulltext_available_here"] is False
    assert [(r["id"], r["value"]) for r in baseline["observations"]] == [
        ("1988_h1", 400), ("1989_h2", 1200), ("1993_h1", 350)]
    assert all(r["unit"] == "column_inches_approx"
               for r in baseline["observations"])
    assert baseline["reported_reliability"]["metric"] == "Scott_pi"
    assert baseline["reported_reliability"]["value"] == 0.78
    assert baseline["reported_reliability"]["not_harrison_recode"] is True
    assert baseline["reproduced_aggregate_statements"] is True
    assert baseline["independent_recode_executed"] is False
    assert baseline["measured_gcc_attributable_effect"] is None
    assert "Published rounded column inches are media ATTENTION volume, not frame-specific percentages" in baseline["design_limitations"]
    assert data["acceptance_gates"][2]["status"] == (
        "published_attention_baseline_located_article_level_GCC_prepost_not_measured")
    second = data["independent_replication"]
    assert second["id"] == "exxon_2021_180"
    assert second["doi"] == "10.1016/j.oneear.2021.04.014"
    assert second["dataverse_doi"] == "10.7910/DVN/XXQUKJ"
    assert second["reported_documents"] == 180
    assert second["published_sample_composition"] == {
        "internal_documents": 32,
        "peer_reviewed_publications": 72,
        "advertorials_taking_any_position": 76,
        "sum": 180,
        "source": "One Earth 2021 Experimental procedures, data and corpora; publisher excerpt",
        "evidence_type": "published_corpus_construction_counts_not_original_document_recode",
        "all_document_provenance_reviewed": False,
    }
    counts = second["published_sample_composition"]
    assert counts["internal_documents"] + counts["peer_reviewed_publications"] + counts["advertorials_taking_any_position"] == counts["sum"]
    assert second["original_180_article_text_available_for_replication"] is False
    assert second["subjects_of_rhetorical_analysis"] == [
        "climate-risk-as-uncertainty",
        "consumer-demand-and-individual-responsibility",
        "fossil-fuel-savior-frame",
    ]
    assert second["original_catalog_in_supplement"] == "S7"
    assert second["access"] == "reasonable request by qualified researchers"
    assert second["original_pdf_reproduction_restricted_by_copyright"]
    assert not second["in_repository_document_level_data"]
    assert not second["replication_executed"]
    assert second["cannot_merge_with_gcc_case_without_source_crosswalk"]
    assert second["original_2017_187_corpus_is_separate"]

    gates = data["acceptance_gates"]
    assert [g["id"] for g in gates] == ["P0","P1","P2","P3","P4","P5"]
    assert all(g["status"] != "complete" for g in gates)
    assert "harrisonFirmCaseHistory" in agda
    assert "gccHeldMediaClippings1993" in agda
    assert "evidenceKindDoesNotFactorThroughGenericTopic" in agda
    assert "noInventedCausalEstimate" in agda
    assert "selectedExxonAccess" in agda
    assert "import DASHI.Cognition.CCDCOEP3Trumbo1996IndependentMediaBaselineExact" in golden
    assert "CCDCOEP3Trumbo1996IndependentMediaBaselineExact.agda" in focused
    assert "import DASHI.Cognition.CCDCOEP3GCCExecutedCampaignSourceExact" in golden
    assert "CCDCOEP3GCCExecutedCampaignSourceExact.agda" in focused
    return {
        "source_index_records": len(sources),
        "bounded_agency_claims": len(claims),
        "agency_self_assessed_impacts": 3,
        "indexed_media_objects": len(media),
        "measured_media_causal_effects": 0,
        "independent_published_attention_windows": len(baseline["observations"]),
        "published_frame_coder_pi": baseline["reported_reliability"]["value"],
        "exxon_2021_documents_reported": second["reported_documents"],
        "exxon_2021_internal_count": counts["internal_documents"],
        "exxon_2021_scientific_count": counts["peer_reviewed_publications"],
        "exxon_2021_advertorial_count": counts["advertorials_taking_any_position"],
        "exxon_2021_reanalysis": "NOT_EXECUTED",
        "remaining_empirical_gates": len(gates),
    }

def main() -> None:
    data = json.loads(MANIFEST.read_text(encoding="utf-8"))
    result = validate(
        data, AGDA.read_text(encoding="utf-8"),
        GOLDEN.read_text(encoding="utf-8"),
        FOCUSED.read_text(encoding="utf-8"))
    print("PASS: source-scoped GCC campaign with self-assessed effects unpromoted")
    print(json.dumps(result, sort_keys=True))

if __name__ == "__main__":
    main()
