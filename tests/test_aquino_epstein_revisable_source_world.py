"""Case-specific data contract checks, not a clone of general Pareto/revision logic.

The reusable consumer model is researched in sibling PR #1268; this child PR
contains only an attributed case fixture and an exact two-operation Agda cut.
Source availability, legal status, kernel proof, and historical truth differ.
"""
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
FIXTURE = ROOT / "docs/receipts/AquinoEpsteinRevisableSourceWorld20261026.json"
BANK = ROOT / "DASHI/Cognition/EpsteinBankingInfrastructureAcquisitionExact.agda"
CASE = ROOT / "DASHI/Cognition/AquinoMaxwellEpsteinCAMaxCutExact.agda"


def world():
    return json.loads(FIXTURE.read_text(encoding="utf-8"))


def test_unique_producers_evidence_claims_and_actions():
    w = world()
    for category in ("sources", "evidence", "claims", "actions"):
        values = [r["id"] for r in w[category]]
        assert len(values) == len(set(values)), category
    roots = {r["id"] for r in w["sources"]}
    evidence = {e["id"] for e in w["evidence"]}
    for e in w["evidence"]:
        assert e["root"] in roots
        assert e["status"] in ("present", "notLocated", "knownAbsent")
        if e["status"] == "present":
            assert e.get("locator", "").startswith("https://")
        if e["status"] == "knownAbsent":
            assert e.get("absence_scope")
    for c in w["claims"]:
        assert c["level"] in ("sourceReported", "independentlyReproduced", "conditional", "unresolved")
        assert set(c["requires"]) <= evidence
        assert set(c.get("supports", [])) <= evidence
        if c["level"] == "independentlyReproduced":
            assert c.get("reproduction_receipt")
    for a in w["actions"]:
        assert a["targets"] and set(a["targets"]) <= evidence
        assert len(a["cost"]) == 3
        assert all(type(x) is int and x >= 0 for x in a["cost"])


def test_one_canadian_root_and_producer_correct_counterfilings():
    w = world()
    roots = {r["id"]: r for r in w["sources"]}
    assert "ONE joint" in roots["canada_joint_2019"]["producer"]
    assert "ONE agency" in roots["ftc_2019_2020"]["producer"]
    assert roots["bannon_defence_2020"]["role"] == "adversarial_respondent_pleading"
    assert roots["ddc_judge_2020"]["role"] == "procedural_judicial_order"
    assert roots["hsi_ipr_2011"]["id"] != roots["dea_ocdetf_2015"]["id"]
    evidence = {e["id"]: e for e in w["evidence"]}
    assert evidence["ftc_bannon_petition_2020"]["root"] == "ftc_2019_2020"
    assert evidence["ftc_bannon_reply_2020"]["root"] == "ftc_2019_2020"
    assert evidence["bannon_opposition_2020"]["root"] == "bannon_defence_2020"
    assert evidence["ddc_show_cause_2020"]["root"] == "ddc_judge_2020"
    assert evidence["black_2016_bank_identity"]["root"] == "future_undetermined_source"
    assert roots["future_undetermined_source"]["role"] == "acquisition_placeholder_not_a_real_source"


def test_present_original_finding_not_same_as_independently_reproduced():
    w = world()
    by_id = {e["id"]: e for e in w["evidence"]}
    claims = {c["id"]: c for c in w["claims"]}
    for c in ("C_CA_AGGREGATE", "C_UK_PAYMENTS", "C_FTC_BANNON_PROCEDURE"):
        assert claims[c]["level"] == "sourceReported"
        assert all(by_id[x]["status"] == "present" for x in claims[c]["requires"])
        assert "reproduction_receipt" not in claims[c]
    assert claims["C_UNIFIED_H3"]["level"] == "unresolved"
    assert not claims["C_UNIFIED_H3"]["supports"]
    assert len(claims["C_UNIFIED_H3"]["requires"]) == 4
    assert "aquino_promis_scl_transfer_native" in claims["C_UNIFIED_H3"]["requires"]
    assert "cross_network_sponsor_budget_original" in claims["C_UNIFIED_H3"]["requires"]


def test_missing_originals_are_unknown_not_negative_facts():
    w = world()
    by_id = {e["id"]: e for e in w["evidence"]}
    for id_ in ("bannon_ftc_final_judgment", "ocdetf_final_disposition",
                "black_2016_bank_identity", "signed_bannon_film_agreement",
                "gsr_to_ripon_exact_nonpii_version", "aquino_promis_scl_transfer_native"):
        assert by_id[id_]["status"] == "notLocated"
        assert "absence_scope" not in by_id[id_]
    assert by_id["ocdetf_derivative_lead_index"]["status"] == "present"
    assert "NOT independently verified" in by_id["ocdetf_derivative_lead_index"]["scope"]


def test_costed_actions_do_not_dominate_distinct_original_objects():
    w = world()
    unknown = {e["id"] for e in w["evidence"] if e["status"] == "notLocated"}
    acts = {a["id"]: a for a in w["actions"]}
    assert len(acts) == 7
    assert set(t for a in acts.values() for t in a["targets"]) == unknown
    # None of these *distinct original-object targets* subsumes another.
    for id_, a in acts.items():
        for other_id, b in acts.items():
            if id_ != other_id:
                assert not set(a["targets"]) >= set(b["targets"])
    # A low-cost item cannot become globally superior by dropping object identity.
    assert acts["A_FTC_DISPOSITION"]["cost"][0] < acts["F_AQUINO_PROMIS"]["cost"][0]


def test_new_original_location_does_not_self_promote_claim_truth():
    w = world()
    claims = {c["id"]: c for c in w["claims"]}
    evidence = {e["id"]: e for e in w["evidence"]}
    claim = claims["C_OCDETF_FINAL"]
    assert claim["level"] == "unresolved"
    assert evidence["ocdetf_final_disposition"]["status"] == "notLocated"
    evidence["ocdetf_final_disposition"]["status"] = "present"  # hypothetical only
    evidence["ocdetf_final_disposition"]["locator"] = "https://example.org/fictional"
    assert claim["level"] == "unresolved"  # requires source interpretation


def test_finite_name_collision_proof_reuses_master_nonfactorability_owner():
    b = BANK.read_text()
    c = CASE.read_text()
    for token in (
        "import DASHI.Core.IntersectionalNonFactorability as NonFactor",
        "originalFederalNameCollisionWitness =",
        "NonFactor.nonFactorabilityWitness",
        "nameOnlyFederalCaseIdentityImpossible =",
        "NonFactor.witnessRulesOutEveryFlatFactorisation",
        "nameReformattingDoesNotResolveFederalCases reformat =",
        "NonFactor.rechartingCannotRecoverErasedPhenomenon",
        "originalCaseKeyConsumerFactors =",
        "NonFactor.factorsThrough keyIdentifiesDEA",
    ):
        assert token in b
    for token in (
        "bankingNameOnlyCaseDecoderNoGo = Banking.nameOnlyFederalCaseIdentityImpossible",
        "bankingAgencyCaseKeyRestoresFiniteConsumer = Banking.originalCaseKeyConsumerFactors",
    ):
        assert token in c


def test_latest_follow_through_severe_bidirectional_contract_is_complete():
    """Case data is compatible with #1268 head's *data* validator, no sibling import."""
    w = world()
    assert w["schema_version"] == "aquino-epstein-source-world-2"
    assert "12f0ba7005572d60152f304863afbf1c7ffa5b8b" in w["latest_sibling_contract"]
    for c in w["claims"]:
        severe = c["severe_test"]
        assert all(severe.get(k) for k in ("would_narrow", "would_strengthen", "test_status"))
        assert severe["test_status"] in ("notRun", "sourceChecked", "executed")
        if c["level"] == "unresolved":
            assert severe["test_status"] == "notRun"
    assert sum(c["severe_test"]["test_status"] == "sourceChecked"
               for c in w["claims"]) == 4
    assert sum(c["severe_test"]["test_status"] == "notRun"
               for c in w["claims"]) == 7


def test_declared_origin_counts_do_not_multiply_ftc_pleadings():
    """Producer diversity is NOT independent corroboration of the allegations."""
    w = world()
    evidence = {e["id"]: e for e in w["evidence"]}
    claims = {c["id"]: c for c in w["claims"]}
    roots = lambda c: {evidence[x]["root"] for x in claims[c]["supports"]}
    assert roots("C_FTC_BANNON_PROCEDURE") == {
        "ftc_2019_2020", "bannon_defence_2020", "ddc_judge_2020"
    }
    assert len(claims["C_FTC_BANNON_PROCEDURE"]["supports"]) == 4
    assert len(roots("C_FTC_BANNON_PROCEDURE")) == 3
    assert roots("C_CA_AGGREGATE") == {"canada_joint_2019"}
    assert roots("C_NAME_COLLISION") == {"dea_ocdetf_2015", "hsi_ipr_2011"}
    assert roots("C_UNIFIED_H3") == set()
    assert "NOT independent datasets" in w["source_root_independence_ceiling"]
    assert w["original_root_count"] == 9
    assert w["unattributed_future_source_placeholders"] == 1
    assert w["original_root_count"] + w["unattributed_future_source_placeholders"] == len(w["sources"])


def test_new_original_object_selectively_reopens_only_affected_consumers():
    w = world()
    claims = {c["id"]: c for c in w["claims"]}
    evidence = {e["id"]: e for e in w["evidence"]}
    def unpaid(c):
        return {id_ for id_ in c["requires"] if evidence[id_]["status"] != "present"}
    before = {id_: unpaid(c) for id_, c in claims.items()}
    assert before["C_FTC_BANNON_FINAL"] == {"bannon_ftc_final_judgment"}
    assert before["C_FTC_BANNON_PROCEDURE"] == set()
    # Hypothetical lawful source acquisition, not an actual historical result.
    evidence["bannon_ftc_final_judgment"]["status"] = "present"
    evidence["bannon_ftc_final_judgment"]["locator"] = "https://example.org/synthetic"
    after = {id_: unpaid(c) for id_, c in claims.items()}
    assert {k for k in claims if before[k] != after[k]} == {"C_FTC_BANNON_FINAL"}
    assert claims["C_FTC_BANNON_FINAL"]["level"] == "unresolved"
    assert claims["C_UNIFIED_H3"]["level"] == "unresolved"


def test_exact_original_evidence_targets_and_claims_have_distinct_pareto_dimensions():
    """Same action cannot become globally dominant by relabelling its target."""
    w = world()
    evidence = {e["id"]: e for e in w["evidence"]}
    actions = w["actions"]
    consumers = {a["id"]: {c["id"] for c in w["claims"]
                 if set(a["targets"]) & set(c["requires"])}
                 for a in actions}
    for a in actions:
        assert all(evidence[t]["status"] == "notLocated" for t in a["targets"])
        assert consumers[a["id"]]
    assert consumers["F_AQUINO_PROMIS"] == {"C_AQUINO_SCL_TRANSFER", "C_UNIFIED_H3"}
    assert consumers["G_SHARED_PROGRAMME"] == {"C_UNIFIED_H3"}
    for i, a in enumerate(actions):
        for b in actions[i+1:]:
            assert not (set(a["targets"]) >= set(b["targets"]) and
                        consumers[a["id"]] >= consumers[b["id"]])
            assert not (set(b["targets"]) >= set(a["targets"]) and
                        consumers[b["id"]] >= consumers[a["id"]])


def test_root_relations_preserve_adversarial_sources_and_different_government_cases():
    w = world()
    sources = {s["id"] for s in w["sources"]}
    relations = w["root_relations"]
    assert len(relations) == 5
    for edge in relations:
        assert edge["left"] in sources and edge["right"] in sources
        assert edge["relation"] and edge["independence"] and edge["case_ref"]
    by_pair = {(r["left"], r["right"]): r for r in relations}
    assert "same_2020_cid_docket" in by_pair[("ftc_2019_2020", "bannon_defence_2020")]["relation"]
    assert "show-cause procedure not FTC allegations" in by_pair[("ftc_2019_2020", "ddc_judge_2020")]["independence"]
    assert "no common case identity" in by_pair[("hsi_ipr_2011", "dea_ocdetf_2015")]["independence"]
    assert "not independent raw-file audits" in by_pair[("canada_joint_2019", "ftc_2019_2020")]["independence"]
    assert "not be substituted as bank-origin" in by_pair[("black_dechert_2021", "future_undetermined_source")]["independence"]


def test_auspol_crosspollination_does_not_manufacture_evidence_roots():
    w = world()
    aus = w["australian_crosspollination"]
    assert aus["thin_owner"].endswith("AustraliaPoliticalEconomySameObjectCrosswalk20261026Exact.agda")
    assert w["original_root_count"] == 9
    assert w["unattributed_future_source_placeholders"] == 1
    paths = {item["id"]: item for item in aus["positive_paths"]}
    assert len(paths) == 15
    assert paths["AUS_HANSON_2025_HOSPITALITY"]["status"] == "original_indexed_not_pdf_face_inspected"
    assert paths["AUS_HANSON_RINEHART_POLICY"]["status"] == "first_person_attributed"
    assert paths["AUS_ONE_NATION_PENSION_POLICY_JAN2025"]["status"] == "original_party_document_published"
    assert "2025-01-15" in paths["AUS_ONE_NATION_PENSION_POLICY_JAN2025"]["original"]
    assert paths["AUS_RINEHART_2021_POLICY_FIRST_PERSON"]["status"] == "first_person_original_pdf_page_visually_inspected"
    assert paths["AUS_HANCOCK_IPA_2022_POLICY_ADVOCACY"]["status"] == "parliamentary_library_quotes_original_submissions_native_submissions_not_inspected"
    assert paths["AUS_WORK_BONUS_2022_CAPPED_LAW"]["status"] == "original_government_limited_enactment"
    assert paths["AUS_ONE_NATION_HQ_PROSPECTIVE_RENT"]["status"] == "primary_party_and_landlord_statements_reported_by_press_no_executed_lease"
    assert paths["AUS_GINA_EPSTEIN_DIRECT"]["status"] == "not_located_not_universally_absent"
    assert "initially denied all contact" in paths["AUS_BANNON_PALMER"]["evidence"]
    assert "one unsolicited call" in paths["AUS_BANNON_PALMER"]["evidence"]
    assert all(p["not_pays"] for p in paths.values())
    assert all(p["original"] and p["carrier"] for p in paths.values())


def test_auspol_aec_future_time_and_sibling_governance_remain_distinct():
    w = world()
    aus = w["australian_crosspollination"]
    targets = {o["id"]: o for o in aus["decisive_remaining_same_object"]}
    assert len(targets) == 6
    assert "2027-02-01" in targets["AUS_FY2025_26_AEC"]["availability"]
    assert "2027-04-22" in targets["AUS_FY2025_26_AEC"]["availability"]
    assert "2027-03-11" in targets["AUS_FY2025_26_AEC"]["availability"]
    assert "Nov17" in targets["AUS_FY2025_26_AEC"]["availability"]
    assert all(t["kind"] and t["claim_reopened"] and t["not_pays"] for t in targets.values())
    assert len(aus["sibling_reviews"]) == 2
    assert all(s["pr"] == 1251 for s in aus["sibling_reviews"])
    assert all(s["integration"] == "review_only_unmerged_sibling" for s in aus["sibling_reviews"])
    assert "is distinct from" in aus["provenance_boundary"]
    assert "cannot be retroactively claimed inspected" in aus["statutory_time_boundary"]


def test_auspol_transfer_not_grafted_onto_existing_us_gsr_or_unified_h3():
    w = world()
    claims = {c["id"]: c for c in w["claims"]}
    assert claims["C_GSR_ROW"]["level"] == "unresolved"
    assert claims["C_UNIFIED_H3"]["level"] == "unresolved"
    assert claims["C_UNIFIED_H3"]["supports"] == []
    aus = w["australian_crosspollination"]
    assert "Canadian" not in aus["causal_boundary"]  # Different legal/country claim sets
    assert "counterfactual evidence" in aus["causal_boundary"]
    assert "Universal" not in aus["causal_boundary"]


def test_australian_policy_original_published_before_attributed_source_and_transition_split():
    world_data = world()
    au = world_data["australian_crosspollination"]
    assert au["original_party_policy_first_party"].startswith("https://www.onenation.org.au/")
    assert au["aec_transitional_original"].endswith("/FADTransitionalRules/")
    assert "2025" in au["original_policy_transmission_ceiling"]
    assert "not a dated original Rinehart instruction" in au["original_policy_transmission_ceiling"]
    assert "2027-02-01" in au["electoral_period_boundary"]
    assert "2027-04-22" in au["electoral_period_boundary"]
    assert "NEW 2027" in au["electoral_period_boundary"]
    assert "AUS_POLICY_ADVICE_TIMESTAMP_AND_ENACTMENT" in {
        t["id"] for t in au["decisive_remaining_same_object"]
    }
    assert "AUS_POLICY_ADOPTION" not in {
        t["id"] for t in au["decisive_remaining_same_object"]
    }


def test_auspol_pre2025_original_speech_2022_independent_partial_legislation_and_proposed_lease():
    w = world()["australian_crosspollination"]
    policy = w["policy_genealogy_same_object_chain"]
    assert len(policy) == 8
    assert [p["date"] for p in policy] == [
        "2021-11-22", "2022-02", "2022-08", "2022-08-16",
        "2022-09-02", "2022-11-22", "2025-01-15", "2026-06-11"
    ]
    assert policy[0]["source_role"] == "first_person_original_pdf_visually_inspected"
    assert "403" in policy[3]["source_role"]
    assert "same government" in policy[2]["source_role"].replace("_", " ")
    assert "limited" in policy[5]["policy_scope"]
    assert "unlimited" in policy[6]["policy_scope"]
    assert "NOT authenticated" in policy[0]["same_object_transfer_to_next"]
    assert w["policy_bidi_severe_test"]["private_message_found"] is False
    assert "National Seniors" in w["policy_bidi_severe_test"]["alternative_mechanism"]
    assert w["commercial_lease_bidi_severe_test"]["material_subsidy_established"] is False
    assert "independently comparable" in w["commercial_lease_bidi_severe_test"]["would_narrow"]
    assert "AUS_HQ_EXECUTED_LEASE" in {t["id"] for t in w["decisive_remaining_same_object"]}
    assert "rather than" not in w["independence_nontransfer"]  # avoid invented editorial instruction


def test_auspol_rinehart_2021_source_and_labour_2022_act_differ_in_policy_scope():
    b = (ROOT / "DASHI/Cognition/AustraliaPoliticalEconomySameObjectCrosswalk20261026Exact.agda").read_text()
    for marker in (
        "rinehart2021PublishedOriginalAdvocacy = australia-source-role-receipt",
        "hancockIPA2022IndexedParliamentaryPolicy = australia-source-role-receipt",
        "albanese2022LimitedWorkBonusAct = australia-source-role-receipt",
        "oneNationBrisbaneHQReportedLease = australia-source-role-receipt",
        "originalFirstPersonPolicyAdvocacy : AustraliaSourceRole",
        "governmentIndexedAdvocacySubmission : AustraliaSourceRole",
        "originalLimitedGovernmentLegislation : AustraliaSourceRole",
        "proposedCommercialPartyTenancyReported : AustraliaSourceRole",
        "temporaryExtraWorkBonus4000 : PensionerWorkPolicyScope",
        "unlimitedPensionWorkWithoutPaymentReduction : PensionerWorkPolicyScope",
        "government2022PolicyScope = temporaryExtraWorkBonus4000",
        "oneNation2025PolicyScope = unlimitedPensionWorkWithoutPaymentReduction",
    ):
        assert marker in b


def test_auspol_recent_climate_claim_family_is_cross_referenced_not_new_independent_root():
    w = world()
    a = w["australian_crosspollination"]
    family = a["sibling_climate_claim_family_crosswalk"]
    assert family["owner_pr"] == 1251
    assert family["owner_head_reviewed"] == "68415b469b4cff67f452fb8c8c1d69476cc5a2ce"
    assert family["sibling_code_imported"] is False
    rows = {r["receipt"]: r for r in family["sibling_related_claims"]}
    assert set(rows) == {"G15", "G16"}
    assert rows["G15"]["originality"] == "explicit credited republication"
    assert "a separate original model" in rows["G15"]["not_pays"]
    assert "Hansard transcript mirror" in rows["G16"]["hosted_by"]
    assert "copied script" in rows["G16"]["not_pays"]
    assert "ONE first-party document" in family["shared_rinehart2021_original"]
    assert "same-object transfer" in family["stopping_rule"]
    assert w["original_root_count"] == 9
    assert w["claims"][0]["level"] == "sourceReported"


def test_2022_national_seniors_original_model_has_named_commissioner_not_empirical_policy_causation():
    w = world()["australian_crosspollination"]
    origins = {p["id"]: p for p in w["positive_paths"]}
    assert origins["AUS_NATIONAL_SENIORS_2022_ORIGINAL_MEMBER_SURVEY"]["status"] == (
        "original_first_party_survey_flyer_pdf_face_visually_inspected"
    )
    assert origins["AUS_NATIONAL_SENIORS_DELOITTE_2022_ORIGINAL_COMMISSION"]["status"] == (
        "original_client_named_commission_pdf_pages_1_and_5_visually_inspected"
    )
    m = w["policy_original_commission_positive_control"]
    assert m["producer"] == "Deloitte Touche Tohmatsu"
    assert "National Seniors Australia" in m["client"]
    assert m["date"] == "2022-09-02"
    assert "page index 0 and page index 4" in m["image_checks"]
    assert "8.3% uptake" in m["relevant_quantitative_claim"]
    assert "not measured real-world uptake" in m["relevant_quantitative_claim"]
    assert "no inspected directed commission" in m["positive_control"]
    assert "Invoice settlement/payment" in m["what_not_proved"]
    assert "Deloitte" in w["policy_bidi_severe_test"]["alternative_mechanism"]
    assert "share NSA commissioning input" in w["independence_nontransfer"]
    b = (ROOT / "DASHI/Cognition/AustraliaPoliticalEconomySameObjectCrosswalk20261026Exact.agda").read_text()
    assert "nationalSeniorsDeloitte2022CommissionedModel = australia-source-role-receipt" in b
    assert "nationalSeniorsMemberCampaign2022Original = australia-source-role-receipt" in b
    assert "originalNamedCommissionedPolicyModel : AustraliaSourceRole" in b
