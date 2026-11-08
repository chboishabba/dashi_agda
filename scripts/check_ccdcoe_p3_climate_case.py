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
        "api_wide_authorisation": "contemporaneous_no_approval_report_final_unidentified",
        "contemporaneous_no_executive_funding_approach": "attributed_interview_as_of_apr_1998",
        "organiser_retrospective_nonexecution": "attributed_secondary_not_independently_verified",
        "later_coalition_advocacy": "bounded_reported",
        "separate_campaign_public_materials": "source_bounded_documented",
        "document_content_divergence": "published_study_result",
        "1998_API_draft_identified_effect": "not_identified",
        "preplan_survey": "reported_in_original_draft_not_independently_validated",
        "actual_1998_plan_expenditure": "not_identified",
        "preexisting_1997_opinion_dynamics": "measured_published_descriptive",
        "specific_1998_plan_nonimplementation": "direct_retrospective_participant_testimony_with_contemporaneous_support_financially_unverified",
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
        "api_wide_authorisation_of_plan":
            "contemporaneous_report_of_no_approval; final_outcome_unidentified",
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
        "independent_1997_climate_opinion_dynamics":
            "measured_independent_pre_1998_API_draft_not_API_effect",
        "specific_1998_draft_contemporaneous_no_funding_solicitation":
            "contemporaneous_report_organiser_executives_not_yet_approached",
        "retrospective_organiser_nonimplementation_account":
            "attributed_secondary_statement_not_final_receipt",
        "named_1998_data_center_never_formed":
            "amicus_assertion_no_independent_registry_witness",
        "former_API_executive_retrospective_nonfunding":
            "direct_attributed_2021_interview_unverified_financially",
        "former_API_executive_corroborates_multi_org_planning":
            "retrospective_named_participant_corrob_primary_workshop",
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
    pre_api = data["independent_pre_api_opinion_panel"]
    assert pre_api["url"] == ("https://www.resources.org/archives/"
                              "american-opinion-on-global-warming-the-impact-of-the-fall-1997-debate/")
    assert [row["n"] for row in pre_api["waves"]] == [688, 725]
    assert [row["end"] for row in pre_api["waves"]] == [
        "1997-10-05", "1998-02-13"]
    assert all(row["end"] < primary["original_plan_date"]
               for row in pre_api["waves"])
    assert pre_api["measured_prior_to_API_draft"] is True
    assert pre_api["cannot_measure_1998_API_plan_impact"] is True
    assert not pre_api["quantitative_microdata_present_in_repo"]
    assert pre_api["causal_effect_of_API_plan"] is None
    values = {row["construct"]: row for row in
              pre_api["published_descriptive_percentages"]}
    assert values["news_exposure_reported_last_4_months"] == {
        "construct": "news_exposure_reported_last_4_months",
        "pre": 48, "post": 56, "delta_percentage_points": 8}
    assert values["thinking_a_lot_or_moderate"] == {
        "construct": "thinking_a_lot_or_moderate",
        "pre": 54, "post": 65, "delta_percentage_points": 11}
    assert values["strong_party_gap_belief_warming_occurred"] == {
        "construct": "strong_party_gap_belief_warming_occurred",
        "pre": 4, "post": 17, "delta_percentage_points": 13}
    assert all(row["post"] - row["pre"] == row["delta_percentage_points"]
               for row in values.values())
    assert data["integration_joins"]["1997_climate_opinion_panel_to_1998_API_plan_effect"].startswith("temporal negative control")
    contemporary = data["contemporaneous_reported_funding_status"]
    assert contemporary["id"] == "nyt_cushman_apr_26_1998_report"
    assert contemporary["source_id"] == primary["id"]
    assert contemporary["publication_date"] == "1998-04-26"
    assert contemporary["verified_accounting_ledger"] is None
    assert contemporary["verified_final_approval_decision"] is None
    claims = contemporary["reported_statements"]
    assert {r["id"] for r in claims} == {
        "joe_walker_no_approach_to_executives",
        "participating_organisations_not_formally_approved"}
    assert all(not r["proves_future_nonfunding"] if
               "proves_future_nonfunding" in r else
               not r["proves_future_nonapproval"] for r in claims)
    retrospective = data["retrospective_plan_nonimplementation_account"]
    assert retrospective["id"] == "walker_retrospective_sourcewatch"
    assert retrospective["source_type"] == (
        "secondary_republication_of_attributed_retrospective_statement")
    assert all(retrospective[key] is None for key in (
        "original_communication_or_interview_receipt",
        "independent_corroboration", "actual_funding_receipt",
        "actual_implementation_receipt"))
    amicus = data["litigation_amicus_unformed_center_claim"]
    assert amicus["id"] == "amicus_9th_circuit_2019_03_20"
    assert amicus["filing_date"] == "2019-03-20"
    assert amicus["case_docket"] == "18-16663"
    assert amicus["source_line_range"] == [1015, 1020]
    assert amicus["document_kind"] == (
        "amicus_brief_in_support_of_plaintiffs_appellants")
    assert all(amicus[key] is None for key in (
        "independent_registry_certificate", "judicial_fact_finding"))
    assert amicus["proves_no_successor_or_equivalent_program"] is False
    assert amicus["proves_total_1998_plan_cancellation"] is False
    interview = data["direct_former_executive_interview"]
    assert interview["id"] == "okeefe_cook_interview_2021"
    assert interview["date"] == "2021-04-20"
    assert interview["url"] == "https://gelbspanfiles.com/?p=11851"
    assert interview["primary_testimony_within_published_interview"] is True
    assert interview["provenance_status"] == (
        "published_named_interview_transcript_not_original_recording")
    assert {r["id"] for r in interview["reported_claims"]} == {
        "2021_direct_nonfunding", "2021_multi_org_workshop",
        "2021_prior_loe_attribution_disputed",
        "2021_no_official_policy_adoption"}
    assert all(r["lines"][0] <= r["lines"][1]
               for r in interview["reported_claims"])
    assert all(interview[k] is None for k in (
        "independent_financial_audit", "company_funding_closeout",
        "independent_implementation_audit"))
    assert data["integration_joins"]["2021_okeefe_to_finance"].startswith(
        "first-person participant assertion")
    assert data["promotion"]["specific_1998_plan_nonimplementation"] == (
        "direct_retrospective_participant_testimony_with_contemporaneous_support_financially_unverified")
    source_lookup = (
        {c["id"] for c in later} | {primary["id"], amicus["id"],
        interview["id"]} |
        {e["id"] for e in activities} | {corpus["id"], pre_api["id"],
        contemporary["id"], retrospective["id"]})
    assert all(set(q["source_ids"]) <= source_lookup
               for q in data["evidence_question_ledger"])
    assert data["integration_joins"][
        "1998_draft_to_2017_later_coalition_activity"
    ].startswith("no direct execution identity")
    assert data["promotion"]["api_wide_authorisation"] == (
        "contemporaneous_no_approval_report_final_unidentified")
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
    # Supran/Oreskes 2020 is a NEW search frame. Do not present
    # 2017 source-type denominators as pooled or revised 2020 estimates.
    versions = data["document_analysis_versions"]
    assert len(versions) == 2
    original, addendum = versions
    assert original["id"] == "supran_oreskes_2017"
    assert original["doi"] == "10.1088/1748-9326/aa815f"
    assert original["total_climate_communications"] == 187
    assert original["advertorials_in_original_study"] == 36
    assert original["advertorials_original_position_takers"] == 26
    assert original["acknowledge_original"] == 3
    assert original["doubt_original"] == 21
    assert addendum["id"] == "supran_oreskes_2020_addendum"
    assert addendum["doi"] == "10.1088/1748-9326/ab89d5"
    assert addendum["retrieved_search_documents"] == 1448
    assert addendum["classified_not_irrelevant_advertorials"] == 267
    assert addendum["advertorials_taking_position_on_real_human_caused"] == 61
    assert 0 < 61 <= 267 <= 1448
    assert all(row["independent_audience_effect_estimate"] is None
               for row in versions)
    transport = data["document_analysis_transport_guard"]
    assert transport["selected_owner"] == "2017_original_187_corpus"
    assert transport["expanded_addendum_owner"] == "2020_newspaper_search"
    assert transport["direct_pooling_authorized"] is False
    assert transport["requires_document_id_crosswalk_and_coding_revision_receipt"]
    assert transport["causal_impact_estimate"] is None
    assert round(100 * original["acknowledge_original"] /
                 original["advertorials_original_position_takers"]) == 12
    assert round(100 * original["doubt_original"] /
                 original["advertorials_original_position_takers"]) == 81
    disposition = data["max_cut_case_disposition"]
    assert disposition["selected_historical_question"].startswith(
        "Was the particular April 3 1998")
    assert disposition["planning_workshop"] == (
        "documented_contemporaneous_draft_and_attested_by_named_participant")
    assert disposition["retrospective_nonimplementation"] == (
        "supported_by_two_named_participant_attributions_not_by_company_accounting")
    assert disposition["epistemic_grade"] == (
        "historically_supported_participant_account_not_independently_audited_final_negative")
    assert disposition["independent_observed_causal_effect"] is None
    assert disposition["future_persuasion_causal_estimand_status"] == (
        "NOT_ADMISSIBLE_FOR_THIS_SPECIFIC_PLAN_UNLESS_IMPLEMENTATION_AND_EXPOSURE_ESTABLISHED")
    assert len(disposition["final_certification_conditions"]) == 4
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
        "contested_authorisation": "CONTEMPORANEOUS_NONAPPROVAL_REPORT_FINAL_UNKNOWN",
        "original_scan_sha256_available": False,
        "plan_execution": "NOT_IDENTIFIED",
        "pre_api_survey_waves_measured": len(pre_api["waves"]),
        "reported_pre_api_descriptive_contrasts": len(values),
        "verified_API_attributable_outcomes": 0,
        "source_gated_decisions": len(ladder),
        "archival_review_leads": len(leads),
        "stage_nonfactorability_witnesses": 4,
        "direct_executive_interviews": 1,
        "signed_financial_closeout": False,
        "case_disposition": disposition["epistemic_grade"],
        "published_study_cohorts": len(versions),
        "cohort_pooling_authorized": False,
    }

def main():
    data = json.loads(MANIFEST.read_text(encoding="utf-8"))
    result = validate(data, CASES.read_text(encoding="utf-8"),
                      SOURCES.read_text(encoding="utf-8"))
    print("CCDCOE P3 climate case manifest: bounded claims validated")
    print(json.dumps(result, sort_keys=True))

if __name__ == "__main__":
    main()
