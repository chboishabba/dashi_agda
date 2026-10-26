"""Consumer-selective DMT motif hyperfabric and Erowid provenance contracts.

Only finite source metadata and synthetic transitions; NO protected Erowid
reports, individual Sanders phase matrices or original PNAS data are read.
"""
import copy
import importlib.util
import json
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location(
    "dmt_motif_hyperfabric", ROOT / "scripts/audit_dmt_motif_hyperfabric.py")
mod = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(mod)


def fixture():
    return mod.load(), mod.load(mod.WORLD), mod.load(mod.EROWID)


def test_hyperfabric_validates_against_existing_world_and_sources():
    h, w, e = fixture()
    assert mod.validate(h, w, e)
    assert len(h["sites"]) == 15 and len(h["edges"]) == 8
    assert h["canonical_origin"]["formal_owner"] == (
        "DASHI.Reasoning.TypedHyperfabricCore")


def test_published_and_constructed_source_levels_are_distinct():
    outcome = mod.audit(*fixture())
    assert set(outcome["published_or_constructed_admitted"]) == {
        "e_published_motif_summary",
        "e_synthetic_recurrence_counterexample",
        "e_published_cross_study_description",
    }
    assert len(outcome["blocked_edges"]) == 5
    assert outcome["no_raw_erowid_data_acquired"]
    assert outcome["no_report_chronology_measured"]
    assert outcome["no_cross_cohort_same_person_join"]
    assert outcome["no_external_agent_inferred"]


def test_published_category_does_not_cause_motif_transition():
    h, w, e = fixture()
    changed = copy.deepcopy(h)
    req = next(x for x in changed["edges"] if x["id"] == "e_report_temporal_transition")
    req["requires"].append("erowid_category")
    with pytest.raises(ValueError, match="Forbidden direct"):
        mod.validate(changed, w, e)


def test_existing_agda_toy_cannot_be_admitted_as_measured_M2():
    h, w, e = fixture()
    edge = next(x for x in h["edges"] if x["id"] == "e_mechanistic_M2_test")
    edge["requires"].append("existing_motif_operator")
    with pytest.raises(ValueError, match="Forbidden direct"):
        mod.validate(h, w, e)


def test_cannot_fabricate_source_rights_or_copyright_permission():
    h, w, e = fixture()
    h1 = copy.deepcopy(h)
    next(x for x in h1["sites"]
         if x["id"] == "erowid_reuse_authority")["state"] = "present_source_statement"
    with pytest.raises(ValueError, match="Governance"):
        mod.validate(h1, w, e)
    e1 = copy.deepcopy(e)
    e1["raw_data_governance"]["permission_obtained"] = True
    with pytest.raises(ValueError, match="rights scope"):
        mod.validate(h, w, e1)


def test_source_world_status_must_not_be_overridden_by_local_bridge():
    h, w, e = fixture()
    new_world = copy.deepcopy(w)
    next(x for x in new_world["artifacts"]
         if x["id"] == "original_static_fd")["status"] = "present"
    with pytest.raises(ValueError, match="re-evaluate original_motion_qc"):
        mod.validate(h, new_world, e)


def test_missing_temporal_receipt_dry_run_is_selective_and_nonmutating():
    h, w, e = fixture()
    original = copy.deepcopy(h)
    candidate = mod.candidate_reopening(h, "erowid_sequenced_report")
    assert candidate["source_state_after"] == "notLocated"
    assert candidate["world_mutated"] is False
    assert candidate["rights_or_measurement_verified"] is False
    assert not candidate["ontology_inferred"]
    assert {edge["edge"] for edge in candidate["would_reopen_only"]} == {
        "e_report_temporal_transition", "e_paired_temporal_claim"}
    assert all(not x["claim_immediately_admitted"] for x in candidate["would_reopen_only"])
    assert h == original


def test_published_source_site_cannot_be_reacquired_as_new_measurement():
    h, _, _ = fixture()
    with pytest.raises(ValueError, match="Only notLocated"):
        mod.candidate_reopening(h, "erowid_category")
    with pytest.raises(ValueError, match="Unknown fibre"):
        mod.candidate_reopening(h, "external_entity_ontology")


def test_focused_agda_bridge_reuses_hyperfabric_and_observer_nonidentification():
    text = mod.FORMAL_SOURCE.read_text(encoding="utf8")
    assert "Fabric.TypedHyperfabric" in text
    assert "Evidence.HiddenCaseEvidence" in text
    assert "Evidence.hiddenCaseEvidenceBlocksPublicDescent" in text
    assert "reportTemporalNeedsPermission" in text
    assert "staticCategoryCannotWitnessTransitions" in text
    assert "staticCategoryCannotWitnessOriginalGFC" in text
    assert "reweightedThreeCycleReturns" in (
        ROOT / "DASHI/Biology/VisualMotifTransitionOperator.agda"
    ).read_text(encoding="utf8")
    assert "DMTMotifObservationHyperfabricExact" in mod.AGGREGATE.read_text(encoding="utf8")


def test_forbidden_edges_cannot_be_removed_by_source_search():
    h, w, e = fixture()
    h["forbidden_edges"] = [x for x in h["forbidden_edges"]
                            if x["from"] != "erowid_category"]
    with pytest.raises(ValueError, match="non-promotion"):
        mod.validate(h, w, e)


def test_ontology_and_original_replay_have_no_silent_incidence():
    outcome = mod.audit()
    assert "e_original_neural_replay" in outcome["blocked_edges"]
    assert "e_mechanistic_M2_test" in outcome["blocked_edges"]
    assert "e_concealed_target_test" in outcome["blocked_edges"]
    assert "M4_independent_external_ontology" not in outcome["published_or_constructed_admitted"]


def test_dry_run_rejects_forged_source_status_before_search():
    h, _, _ = fixture()
    bad = copy.deepcopy(h)
    next(x for x in bad["sites"]
         if x["id"] == "erowid_sequenced_report")["state"] = "present_source_statement"
    with pytest.raises(ValueError, match="promoted"):
        mod.candidate_reopening(bad, "erowid_reuse_authority")
