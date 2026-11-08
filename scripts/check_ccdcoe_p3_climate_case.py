#!/usr/bin/env python3
"""Fail-closed source-bound CCDCOE P3 climate genealogy demonstrator.

This checks a bounded scholarly genealogy already represented in original
Agda owners. It checks source-location anchors but does NOT create raw document hashes,
identified causal effects, command records, or psychological measurements.
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
        "api_wide_authorisation": "contested_not_identified",
        "later_coalition_advocacy": "bounded_reported",
        "separate_campaign_public_materials": "source_bounded_documented",
        "document_content_divergence": "published_study_result",
        "1998_API_draft_identified_effect": "not_identified",
        "preplan_survey": "reported_in_original_draft_not_independently_validated",
        "actual_1998_plan_expenditure": "not_identified",
    }
    later = data["followup_evidence_20261107"]
    assert {item["id"] for item in later} == {
        "api_response_1998_05_01",
        "coalition_investigation_2017_09_05",
        "house_hearing_2019_10_23",
    }
    assert all(item["date"] and item["url"].startswith("https://")
               and item["source_line_ranges"] for item in later)
    assert all(item["operational_primary_receipt"] is False
               for item in later)
    assert later[0]["source_type"] == "contemporaneous_attributed_response"
    assert later[1]["source_type"] == "later_investigative_reporting"
    assert later[2]["source_type"] == "official_hearing_transcript_with_testimony"
    question_status = {row["id"]: row["status"]
                       for row in data["evidence_question_ledger"]}
    assert question_status == {
        "public_1998_draft": "documented_primary",
        "planning_group_and_proposed_actions": "documented_primary",
        "api_wide_authorisation_of_plan": "contested_not_identified",
        "independently_reported_later_coalition_advocacy":
            "reported_independent_later_activity",
        "specific_1998_plan_implementation": "not_identified",
        "campaign_exposure_and_impact": "not_identified",
        "plan_caused_Kyoto_or_Paris_policy_outcome": "not_identified",
        "separate_climate_advocacy_implemented_elsewhere":
            "documented_separate_examples_not_API_draft_execution",
        "corporate_message_divergence_in_published_corpus":
            "quantified_document_content_not_causal_effect",
        "charlton_preplan_survey_reported":
            "reported_survey_not_causal_effect",
    }
    activities = data["independent_activity_and_document_measurements"]
    assert {e["id"] for e in activities} == {
        "ice_1991_advertising", "gcc_1995_public_handout",
        "cooler_heads_1998_event_invitation", "gcc_1996_primer_review"}
    assert all(event["same_plan_as_1998_api"] is False for event in activities)
    assert all(event["audience_persuasion_effect"] is None for event in activities)
    assert all(event["source_url"].startswith("https://") and event["primary_item_locator"] for event in activities)
    assert next(event for event in activities if event["id"] ==
                "cooler_heads_1998_event_invitation")["implementation_class"] == (
                "invitation_and_scheduled_event_documented")
    corpus = data["published_document_content_measurement"]
    assert corpus["doi"] == "10.1088/1748-9326/aa815f"
    assert corpus["document_count"] == 187
    assert corpus["reported_percentages"] == {
        "peer_reviewed_acknowledge_human_cause": 83,
        "internal_acknowledge_human_cause": 80,
        "advertorial_acknowledge_human_cause": 12,
        "advertorial_doubt_human_cause": 81}
    assert corpus["advertorial_position_subset"] == {
        "all_advertorial_documents": 36,
        "taking_position_on_real_and_human_caused": 26,
        "acknowledge_count": 3,
        "doubt_count": 21,
        "denominator_note": corpus["advertorial_position_subset"]["denominator_note"],
    }
    assert "3/26" in corpus["advertorial_position_subset"]["denominator_note"]
    assert "21/26" in corpus["advertorial_position_subset"]["denominator_note"]
    assert corpus["advertorial_position_subset"]["doubt_count"] + corpus[
        "advertorial_position_subset"]["acknowledge_count"] <= corpus[
        "advertorial_position_subset"]["taking_position_on_real_and_human_caused"]
    assert corpus["outcome_type"] == "document_coding_by_source_type_not_people"
    assert not corpus["has_original_microdata_in_repo"]
    assert corpus["causal_effect_on_readers"] is None
    assert data["integration_joins"]["1991_ICE_1995_GCC_1998_CoolerHeads_to_1998_API_draft"].startswith("independent events")
    assert data["integration_joins"]["2017_document_coding_to_1998_API_exposure_effect"].startswith("different observational outcome")
    source_lookup = {c["id"] for c in later} | {primary["id"]} | {e["id"] for e in activities} | {corpus["id"]}
    assert all(set(q["source_ids"]) <= source_lookup
               for q in data["evidence_question_ledger"])
    assert data["integration_joins"][
        "1998_draft_to_2017_later_coalition_activity"
    ].startswith("no direct execution identity")
    assert data["promotion"]["api_wide_authorisation"] == (
        "contested_not_identified")
    assert data["promotion"]["later_coalition_advocacy"] == (
        "bounded_reported")
    survey = data["reported_preplan_survey"]
    assert survey["source_id"] == primary["id"]
    assert survey["named_pollster"] == "Charlton Research"
    assert survey["reported_sample_size"] == 1100
    assert survey["reported_response_percent"] == 58
    assert survey["kind"] == "quoted_plan_description_of_preplan_self_report_under_specific_prompt"
    assert all(survey[field] is False for field in (
        "methodology_or_original_poll_instruments_available",
        "representativeness_verified", "randomised_assignment_verified",
        "verified_pre_post_outcome"))
    assert survey["causal_effect_of_1998_plan"] is None
    budgets = data["planned_spending_not_receipts"]
    assert budgets["source_id"] == primary["id"]
    assert budgets["media_program_proposed_usd"] == 600000
    assert budgets["science_center_two_year_proposed_usd"] == 5000000
    assert budgets["direct_outreach_program_proposed_usd"] == 300000
    assert budgets["total_required_through_nov_1998_proposed_usd"] == 2000000
    assert budgets["actual_spent_usd"] is None
    assert budgets["actual_authorised_usd"] is None
    assert data["promotion"]["preplan_survey"] == (
        "reported_in_original_draft_not_independently_validated")
    assert data["promotion"]["actual_1998_plan_expenditure"] == "not_identified"
    # The public April 1998 primary document itself orders the proposed
    # launch AFTER approval, funding, and resource arrangements.
    decision = data["primary_plan_decision_gate"]
    assert decision["source_id"] == primary["id"]
    assert decision["source_url"] == primary["url"]
    assert decision["draft_circulation_line_range"] == [434, 442]
    assert decision["conditional_launch_line_range"] == [659, 664]
    assert decision["observed_draft"] is True
    assert all(decision[name] is False for name in (
        "observed_signed_approval",
        "observed_disbursement",
        "observed_same_plan_delivery",
        "observed_causal_response",
    ))
    assert all(decision[name] is None for name in (
        "approval_receipt_id", "financial_receipt_id",
        "delivered_event_receipt_id", "effect_study_id",
    ))
    ladder = data["evidence_ladder"]
    assert [row["stage"] for row in ladder] == [
        "published_draft",
        "organizational_approval",
        "plan_funding",
        "plan_specific_delivery",
        "causal_belief_or_policy_effect",
    ]
    assert [row["status"] for row in ladder] == [
        "observed_primary",
        "contested_not_identified",
        "not_identified",
        "not_identified",
        "not_identified",
    ]
    assert ladder[0]["actual_receipt"] == primary["id"]
    assert all(row["actual_receipt"] is None for row in ladder[1:])
    # Independently indexed API/GCC documents remain a *discovery* surface;
    # no inferred same-object execution identity.
    leads = data["additional_archival_discovery"]
    assert {row["id"] for row in leads} == {
        "api_feb_1998_rapid_response_draft", "gcc_jul_1995_board_report"
    }
    assert all(row["evidence_status"] ==
               "index_located_original_source_review_pending"
               for row in leads)
    assert all(row["source_url"].startswith("https://") for row in leads)
    assert all(row["same_as_april_plan_execution"] is not True for row in leads)
    # Exact finite observation-ladder counterexamples corresponding to
    # CCDCOEP3EvidenceStageIdentificationExact, not a real-world sample.
    worlds = [
        (True, False, False, False, False),
        (True, True, False, False, False),
        (True, True, True, False, False),
        (True, True, True, True, False),
        (True, True, True, True, True),
    ]
    for coarse, fine in ((0, 1), (1, 2), (2, 3), (3, 4)):
        assert any(
            left[coarse] == right[coarse] and left[fine] != right[fine]
            for left in worlds for right in worlds
        ), f"Unexpected stage factorisation: {coarse} -> {fine}"
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
        "independent_followup_sources": len(later),
        "separate_activities": len(activities),
        "published_communications_analysed": corpus["document_count"],
        "audience_effect_of_1998_API": "NOT_IDENTIFIED",
        "preplan_survey_reported_n": survey["reported_sample_size"],
        "reported_preplan_framing_response_pct": survey["reported_response_percent"],
        "contested_authorisation": "NOT_IDENTIFIED",
        "original_scan_sha256_available": False,
        "plan_execution": "NOT_IDENTIFIED",
        "real_measured_outcomes": 0,
        "source_gated_decisions": len(ladder),
        "archival_review_leads": len(leads),
        "stage_nonfactorability_witnesses": 4,
    }

def main():
    data = json.loads(MANIFEST.read_text(encoding="utf-8"))
    result = validate(data, CASES.read_text(encoding="utf-8"),
                      SOURCES.read_text(encoding="utf-8"))
    print("CCDCOE P3 climate case manifest: bounded claims validated")
    print(json.dumps(result, sort_keys=True))

if __name__ == "__main__":
    main()
