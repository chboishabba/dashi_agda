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
