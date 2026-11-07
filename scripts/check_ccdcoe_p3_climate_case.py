#!/usr/bin/env python3
"""Fail-closed source-bound CCDCOE P3 climate genealogy demonstrator.

This checks a bounded scholarly genealogy already represented in original
Agda owners. It does NOT supply primary-document spans, identified causal
effects, command records, or observed human psychological measurements.
"""
from __future__ import annotations
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "Docs/research/ccdcoe_p3_climate_case_manifest.json"
CASES = ROOT / "DASHI/Governance/EvidenceGradedGenealogyCasesExact.agda"
SOURCES = ROOT / "DASHI/Governance/DevelopmentalInfluenceSourceAtlas.agda"
GRADE_B = "gradeB"
GRADE_C = "gradeC"

def validate(data: dict, cases: str, sources: str) -> dict:
    assert data["schema"] == "dashi.ccdcoe.p3.climate_case.v1"
    assert len(data["documented_edges"]) == 1
    edge = data["documented_edges"][0]
    assert edge["evidence_grade"] == "B"
    assert edge["relation"] == "personnelInstitutionalContinuity"
    assert edge["agda_owner"].endswith("::tobaccoToClimateHistoricalContinuity")
    assert "tobaccoToClimateHistoricalContinuity : Genealogy.EvidenceEdge" in cases
    assert "Genealogy.personnelInstitutionalContinuity" in cases
    assert "Genealogy.gradeB" in cases
    assert "tobaccoToClimateIsStrong" in cases
    assert "wellnessAdjacencyIsNotStrongHistoricalTransfer" in cases
    assert len(data["citation_refs"]) == 2
    source_ids = {s["id"] for s in data["citation_refs"]}
    assert len(source_ids) == 2
    assert set(edge["source_ids"]) == source_ids
    for citation in data["citation_refs"]:
        assert citation["source_owner"].split("::")[-1] in sources
        assert citation["identifier"]
        # No fabricated primary excerpts, line offsets, or revision hashes.
        assert citation["original_document_span"] is None
        assert citation["original_revision_hash"] is None
    assert data["comparator"]["evidence_grade"] == "C"
    assert data["comparator"]["relation"] == "audienceContentAdjacency"
    assert "wellnessToAntiVaxAdjacency" in cases
    assert {h["id"] for h in data["hypotheses"]} == {
        "decentralised_continuity", "central_command", "mixed_relations"}
    assert all(h["historical_edge_id"] == edge["id"] for h in data["hypotheses"])
    assert all(h["status"] == "candidate" and not h["source_supported"]
               for h in data["hypotheses"])
    assert len({h["command_structure"] for h in data["hypotheses"]}) == 3
    assert edge["observed_campaign_effect"] is None
    assert edge["observed_command_structure"] is None
    primary = data["primary_publication"]
    assert primary["url"] == ("https://www.govinfo.gov/content/pkg/"
                              "CREC-1998-04-27/html/CREC-1998-04-27-pt1-PgH2323.htm")
    assert primary["original_plan_date"] == "1998-04-03"
    assert primary["publication_date"] == "1998-04-27"
    assert primary["original_scan_sha256"] is None
    claims = data["primary_plan_claims"]
    assert len(claims) == 6
    claim_ids = {claim["id"] for claim in claims}
    assert len(claim_ids) == 6
    for claim in claims:
        assert claim["source_id"] == primary["id"]
        assert 425 <= claim["line_start"] <= claim["line_end"] <= 795
        assert claim["kind"] in ("documented_planning", "documented_intention",
                                  "documented_proposal")
        assert claim["implementation_status"] == "not_verified"
    assert set(data["observations"]["documented_plan_content"]) == claim_ids
    intake = data["pnf_candidate_intake"]
    assert len(intake) == len(claim_ids)
    assert {r["candidate_id"] for r in intake} == {
        "pnf-" + claim_id for claim_id in claim_ids}
    assert data["pnf_ingestion_status"].startswith(
        "source_locator_and_candidate_roles_created")
    for row in intake:
        assert row["source_id"] == primary["id"]
        assert row["source_locator"] == primary["url"]
        assert row["source_event_time"] == "1998-04-03"
        assert row["source_publication_time"] == "1998-04-27"
        assert row["modality"] == "proposed_or_recorded_in_source"
        assert row["candidate_only"] is True
        assert row["candidate_validity"] == "undetermined"
        assert row["claim_scope"] == "claim_about_published_draft_only"
        assert all(row[key] is None for key in (
            "source_observation_time", "source_ingestion_time",
            "original_text_offset", "parser_profile",
            "semantic_review_receipt", "source_content_hash"))
    assert data["integration_joins"][
        "congressional_draft_to_implementation"] == "not_identified"
    assert data["integration_joins"][
        "congressional_draft_to_realised_policy_effect"] == "not_identified"
    for name, observations in data["observations"].items():
        if name not in ("published_historical_genealogy",
                        "documented_plan_content"):
            assert observations == [], (name, "unpaid observation was fabricated")
    assert data["observations"]["published_historical_genealogy"] == "grade_B_documented"
    assert data["promotion"] == {
        "historical_continuity": "bounded_supported",
        "single_central_command": "not_identified",
        "causal_effect": "not_identified",
        "hostile_intent": "not_identified",
        "population_level_radicalisation": "not_identified",
        "documented_joint_planning": "source_supported",
        "plan_execution": "not_identified",
    }
    assert not data["follow_up_discriminator"]["currently_observed"]
    assert data["follow_up_discriminator"]["source_type_required"] == (
        "original_document_with_provenance")
    return {
        "bounded_genealogy": "SOURCE-REGISTERED",
        "evidence_grade": GRADE_B,
        "generic_label_grade_distinction": f"{GRADE_B}!={GRADE_C}",
        "historical_hypotheses": 3,
        "causal_effect": "NOT_IDENTIFIED",
        "hostile_intent": "NOT_IDENTIFIED",
        "primary_record_span_anchors": len(claims),
        "candidate_pnf_intake_rows": len(intake),
        "original_scan_sha256_available": False,
        "plan_execution": "NOT_IDENTIFIED",
        "real_measured_outcomes": 0,
    }

def main():
    data = json.loads(MANIFEST.read_text(encoding="utf-8"))
    result = validate(data, CASES.read_text(encoding="utf-8"),
                      SOURCES.read_text(encoding="utf-8"))
    print("CCDCOE P3 climate case manifest: bounded claims validated")
    print(json.dumps(result, sort_keys=True))

if __name__ == "__main__":
    main()
