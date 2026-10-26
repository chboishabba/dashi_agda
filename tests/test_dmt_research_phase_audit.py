"""Regression tests for DMT source-first phase and preregistration design contracts."""
from copy import deepcopy
import importlib.util
import json
from pathlib import Path
import pytest

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location(
    "dmt_phase_audit", ROOT/"scripts/audit_dmt_research_phase.py")
audit = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(audit)


def fixtures():
    return [
        json.loads(p.read_text(encoding="utf8")) for p in (
            ROOT/"Docs/receipts/DMT2023SourceWorld.json",
            ROOT/"Docs/receipts/DMT2023DeweyIbrahimAcquisitionDecision20261024.json",
            ROOT/"Docs/receipts/DMTRestrictedModelCards20261024.json"
        )
    ]


def test_phase_audit_consumer_specific_statuses():
    w, d, m = fixtures()
    report = audit.summary(w, d, m)
    assert report["evidence_status_counts"] == {
        "present": 5, "notLocated": 14, "knownAbsent": 2}
    assert report["claims_by_state"] == {
        "source_attested_only": 5,
        "acquisition_blocked": 7,
        "source_scope_blocked": 2,
    }
    assert report["public_mat_only_original_replay"] == "no_declared_source_route"
    assert report["data_fetched"] is False
    assert report["original_fmri_result_reproduced"] is False
    assert report["pre_registration_completed"] is False


def test_four_incomparable_live_source_targets():
    w, d, m = fixtures()
    report = audit.summary(w, d, m)
    assert {x["id"] for x in report["live_research_frontier"]} == {
        "a_original_motion_primary", "b_rights_review",
        "e_phase_matrices", "h_effective_static_code",
    }
    assert report["conditional_static_gfc_route"] == [
        "a_original_motion_primary", "b_rights_review",
        "g_voxel_and_atlas_source", "h_effective_static_code", "d_replay_static",
    ]
    assert "c_source_bytes" not in report["conditional_static_gfc_route"]


def test_source_target_cannot_advertise_unrelated_consumer_gain():
    w, d, m = fixtures()
    wrong = next(x for x in d["source_search"] if x["id"] == "sanders_phases")
    wrong["target_consumers"].append("c_original_static_inclusion")
    with pytest.raises(ValueError, match="False action/consumer fanout"):
        audit.validate_research_contract(w, d, m)


def test_cannot_elevate_doi_ddc_or_qid_metadata_to_unverified_class():
    w, d, m = fixtures()
    d["navigation"]["subject_lenses"][0]["dewey"] = "neuroscience:unverified-number"
    with pytest.raises(ValueError, match="DDC/QID"):
        audit.validate_research_contract(w, d, m)


def test_missing_attributed_producer_is_invalid():
    w, d, m = fixtures()
    d["source_search"][0]["producer"] = ""
    with pytest.raises(ValueError, match="source-specific completion test"):
        audit.validate_research_contract(w, d, m)


def test_model_outcome_must_be_same_across_M0_M1_M2():
    w, d, m = fixtures()
    m["models"][2]["observation_dictionary"] = "hidden_target_not_in_original_fmri"
    with pytest.raises(ValueError, match="matched observation dictionary"):
        audit.validate_research_contract(w, d, m)


def test_reuses_subject_exclusive_split():
    w, d, m = fixtures()
    m["shared_contract"]["same_split"]["unit"] = "fmri_window"
    with pytest.raises(ValueError, match="Subject paired-condition split"):
        audit.validate_research_contract(w, d, m)


def test_fixed_Q_M2_is_not_unique_ontology():
    w, d, m = fixtures()
    m["models"][2]["nonpromotion"] = "Proof of external independent entities"
    with pytest.raises(ValueError, match="generic Markov no-uniqueness"):
        audit.validate_research_contract(w, d, m)


def test_experiment_M3_M4_do_not_auto_become_observed():
    w, d, m = fixtures()
    m["independent_consumers"][0]["status"] = "completed"
    with pytest.raises(ValueError, match="Unapproved M3/M4"):
        audit.validate_research_contract(w, d, m)


def test_unlocated_primary_material_is_not_promoted_by_dossier():
    w, d, m = fixtures()
    assert not any(x.get("status") == "present" for x in w["artifacts"]
                   if x["id"] in ("original_static_fd","original_preprocessed_voxel_nifti",
                                  "original_schaefer_extended_mask","sanders_phase_data",
                                  "effective_static_gfc_workspace"))
    first = next(x for x in d["source_search"] if x["id"] == "motion_qc")
    first["status"] = "completed"
    # A narrative status never creates a measured source object.
    before = deepcopy(w)
    report = audit.summary(w, d, m)
    assert report["original_fmri_result_reproduced"] is False
    assert w == before


def test_full_strawman_control_includes_active_inference_and_HMM_ceiling():
    w, d, m = fixtures()
    report = audit.summary(w, d, m)
    assert report["adversarial_comparators"] == ["M0", "M1a", "M1b", "M2"]
    assert "non-identifiability" in report["highest_value_unconditional_gap"]
    assert report["original_fmri_result_reproduced"] is False


def test_losing_mechanistic_donor_does_not_leave_strong_M1_claim():
    w, d, m = fixtures()
    m["models"][1]["serious_endogenous_donors"] = []
    with pytest.raises(ValueError, match="Mago 2026"):
        audit.validate_research_contract(w, d, m)


def test_generic_trace_no_go_is_required_for_agent_inference():
    w, d, m = fixtures()
    m["models"][2]["ontology_not_identified_by_finite_HMM_trace"] = False
    with pytest.raises(ValueError, match="Fixed-Q trace"):
        audit.validate_research_contract(w, d, m)


def test_existing_erowid_motif_source_remains_connected():
    w, d, m = fixtures()
    assert audit.validate_research_contract(w, d, m) is True
    assert m["recurring_motif_prior_art"].endswith(
        "DMTRecurringMotifErowidPriorArtBridge20261025.json")


def test_erowid_source_reuse_does_not_pretend_raw_narratives_are_available(tmp_path, monkeypatch):
    w, d, m = fixtures()
    import json
    from pathlib import Path
    bridge_path = ROOT / m["recurring_motif_prior_art"]
    b = json.loads(bridge_path.read_text(encoding="utf8"))
    b["raw_data_governance"]["raw_report_corpus_acquired"] = True
    replacement = tmp_path / "false_motif_bridge.json"
    replacement.write_text(json.dumps(b), encoding="utf8")
    original_read = Path.read_text
    def intercepted_read(path, *args, **kwargs):
        if Path(path) == bridge_path:
            return original_read(replacement, *args, **kwargs)
        return original_read(path, *args, **kwargs)
    monkeypatch.setattr(Path, "read_text", intercepted_read)
    with pytest.raises(ValueError, match="falsely promoted"):
        audit.validate_research_contract(w, d, m)


def test_motif_hyperfabric_integrated_into_shared_model_design():
    w, d, m = fixtures()
    report = audit.summary(w, d, m)
    assert m["motif_observation_hyperfabric"] == (
        "Docs/receipts/DMTMotifObservationHyperfabric20261025.json")
    assert set(report["motif_hyperfabric_admitted"]) == {
        "e_published_motif_summary",
        "e_synthetic_recurrence_counterexample",
        "e_published_cross_study_description",
    }
    assert report["original_fmri_result_reproduced"] is False


def test_motif_hyperfabric_dependency_cannot_be_silently_dropped():
    w, d, m = fixtures()
    del m["motif_observation_hyperfabric"]
    with pytest.raises(ValueError, match="Hyperfabric"):
        audit.validate_research_contract(w, d, m)
