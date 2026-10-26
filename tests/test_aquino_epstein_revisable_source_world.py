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
