"""Source-world validation/proof-search contracts, NOT proof of paper results."""
import copy
import importlib.util
from pathlib import Path
import pytest

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location(
    "dmt_world_search", ROOT/"scripts/dmt_source_world_search.py")
engine = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(engine)


def world():
    return engine.load_world()


def test_original_source_tree_and_lineages_are_exact():
    w = world()
    assert len(w["observed_git_tree"]["files"]) == 56
    assert len([x for x in w["observed_git_tree"]["files"]
                if x["path"].startswith("fMRI/LongS")
                and x["path"].endswith(("DMT.mat", "PCB.mat"))]) == 40
    assert any(x["path"] == "fMRI/temp"
               for x in w["observed_git_tree"]["files"])
    assert w["counts"]["repository_paired_subjects"] == 20
    assert w["counts"]["original_pnas_static_n"] == 16
    assert w["counts"]["readme_unspecified_n"] == 15
    assert w["safety"]["send_email"] is False
    sources = {s["id"]: s for s in w["sources"]}
    assert sources["source_eeg_repro"]["lineage_root"] == "pnas2023"
    assert sources["pnas_reanalysis2025"]["lineage_root"] == "pnas2023"


def test_source_claim_is_not_empirical_reproduction():
    result = {x["consumer"]: x for x in engine.claim_status(world())}
    assert result["c_public_files"]["state"] == "source_attested_only"
    assert result["c_static_reproduction"]["state"] == "acquisition_blocked"
    assert "original_static_fd" in result["c_static_reproduction"]["missing"]
    assert "data_use_review" in result["c_static_reproduction"]["missing"]
    assert result["c_external_entity"]["state"] == "acquisition_blocked"
    assert result["c_published_precursor"]["state"] == "source_attested_only"


def test_acquisition_frontier_does_not_claim_promotion():
    candidates = {x["id"]: x for x in engine.action_candidates(world())}
    assert candidates["a_original_motion_primary"]["state"] == "candidate_admissible"
    assert candidates["b_rights_review"]["state"] == "candidate_admissible"
    assert candidates["c_source_bytes"]["state"] == "source_prerequisite_blocked"
    assert candidates["d_replay_static"]["state"] == "source_prerequisite_blocked"
    assert candidates["e_phase_matrices"]["state"] == "candidate_admissible"
    assert not any(x["promotion_authorised"] for x in candidates.values())
    # Pareto must respect WHICH consumer is affected, not merely count leaves:
    # Sanders phase matrices are not "dominated" by a cheaper neural-QC search.
    assert candidates["a_original_motion_primary"]["pareto"]
    assert candidates["b_rights_review"]["pareto"]
    assert candidates["e_phase_matrices"]["pareto"]
    assert candidates["h_effective_static_code"]["pareto"]
    assert candidates["g_voxel_and_atlas_source"]["state"] == "source_prerequisite_blocked"


def test_shortest_hypothetical_paths_are_not_acquisitions():
    w = world()
    before = copy.deepcopy(w)
    static = engine.hypothetical_plan(w, "c_static_reproduction")
    assert static["status"] == "conditional_plan_only"
    assert static["hypothetical_actions"] == [
        "a_original_motion_primary", "b_rights_review",
        "g_voxel_and_atlas_source",
        "h_effective_static_code", "d_replay_static"]
    assert static["evidence_created"] is False
    precursor = engine.hypothetical_plan(w, "c_temporal_replication")
    assert precursor["hypothetical_actions"] == ["e_phase_matrices"]
    assert w == before


def test_malformed_source_dependency_fails_closed():
    w = world()
    w["source_dependencies"].append({
        "from": "pnas_reanalysis2025", "to": "pnas2023",
        "type": "independent_replication"})
    with pytest.raises(ValueError, match="independent replication"):
        engine.validate_world(w)


def test_missing_evidence_not_known_absent_and_rights_not_implied():
    w = world()
    art = next(x for x in w["artifacts"] if x["id"] == "data_use_review")
    assert art["status"] == "notLocated"
    art["status"] = "knownAbsent"
    with pytest.raises(ValueError, match="negative-search"):
        engine.validate_world(w)
    art["status"] = "present"
    with pytest.raises(ValueError, match="specific locator"):
        engine.validate_world(w)


def test_dangling_artifacts_and_unsafe_actuation_are_rejected():
    w = world()
    w["claims"][0]["requires"].append("imaginary_author_permission")
    with pytest.raises(ValueError, match="nonexistent"):
        engine.validate_world(w)
    w = world()
    w["safety"]["send_email"] = True
    with pytest.raises(ValueError, match="External contact"):
        engine.validate_world(w)


def test_agda_source_world_instantiates_existing_reopening():
    path = ROOT/"DASHI/Cognition/ConsciousRealismDMTSourceWorldExact.agda"
    text = path.read_text(encoding="utf8")
    assert "import DASHI.Core.AttributedSourceCore" in text
    assert "import DASHI.Core.EvidenceAcquisitionSelectiveReopeningExact" in text
    assert "import DASHI.Core.CostedResidualInformationChoiceExact" in text
    assert "Acquire.obligationFromNotLocated" in text
    assert "Acquire.oneEdgeAcquisitionReopening" in text
    assert "qcDoesNotDirectlyEstablishExternalAgent" in text
    assert "phaseMatricesDoNotDirectlyEstablishExternalAgent" in text
    focus = (ROOT/"DASHI/Cognition/ConsciousRealismDMTEverything.agda").read_text()
    assert "ConsciousRealismDMTSourceWorldExact" in focus


def test_source_world_mutation_of_exact_git_inventory_fails():
    w = world()
    w["observed_git_tree"]["files"][0]["git_blob_sha1"] = "0" * 40
    with pytest.raises(ValueError, match="diverges"):
        engine.validate_world(w)


def test_20_author_code_subject_ids_match_git_pairs_without_qc_promotion():
    w = world()
    ids = next(a for a in w["artifacts"] if a["id"] == "source_subject_namespace")
    assert len(ids["subject_ids"]) == 20
    assert w["counts"]["distinct_lineage_roots"] == 3
    assert len(w["sources"]) == 7
    evidence = {c["consumer"]: c for c in engine.claim_status(w)}
    assert evidence["c_verified_source_namespace"]["state"] == "source_attested_only"
    assert evidence["c_original_static_inclusion"]["state"] == "acquisition_blocked"
    ids["subject_ids"][0] = "S99"
    with pytest.raises(ValueError, match="disagree"):
        engine.validate_world(w)


def test_missing_dynamic_helper_is_known_absent_only_in_pinned_tree():
    w = world()
    helper = next(a for a in w["artifacts"]
                  if a["id"] == "dynamic_tapered_window_in_pinned_tree")
    assert helper["status"] == "knownAbsent"
    assert "pinned" in helper["scope"] or "source Git tree" in helper["scope"]
    assert "negative_search_receipt" in helper
    result = engine.hypothetical_plan(w, "c_dynamic_replay_from_tree_alone")
    assert result["status"] == "no_declared_source_route"
    assert result["evidence_created"] is False


def test_source_roots_count_lineage_not_documents():
    snap = engine.snapshot(world())
    assert snap["source_records"] == 7
    assert snap["bibliographic_lineage_roots"] == 3
    assert snap["participant_independence_certified"] is False
    assert snap["artifact_status_counts"] == {
        "knownAbsent": 2, "notLocated": 14, "present": 5}


def test_candidate_tip_selectively_reopens_without_changing_world():
    w = world()
    before = copy.deepcopy(w)
    proposal = {
        "source_id": "pnas2023",
        "source_locator": "https://example.org/SYNTHETIC-ONLY-qc.csv",
        "source_revision": "SYNTHETIC-TEST",
        "candidate_sha256": "f" * 64,
        "access_scope": "UNVERIFIED SYNTHETIC",
        "observation_time": "2026-10-24",
        "verification_method": "NONE -- fixture",
    }
    result = engine.candidate_source_receipt(w, "original_static_fd", proposal)
    assert result["status"] == "candidate_tip_not_admitted"
    assert result["world_mutated"] is False
    assert result["artifact_status_after"] == "notLocated"
    consumers = {x["consumer"] for x in result["would_reopen_consumers"]}
    assert consumers == {
        "c_original_static_inclusion", "c_original_dynamic_inclusion",
        "c_original_joint_inclusion", "c_static_reproduction"}
    assert "c_external_entity" not in consumers
    assert "c_public_mat_reproduces_original_static" not in consumers
    assert result["source_scope_blocked_consumers_not_reopened"] == [
        "c_public_mat_reproduces_original_static"]
    assert w == before


def test_candidate_tip_cannot_assert_authority_or_fix_known_absent():
    w = world()
    evidence = {
        "source_id": "pnas2023",
        "source_locator": "https://example.org/not-a-real-source",
        "source_revision": "synthetic",
        "candidate_sha256": "0" * 64,
        "access_scope": "none",
        "observation_time": "2026-10-24",
        "verification_method": "unverified",
    }
    bad = dict(evidence, source_id="sanders2026")
    with pytest.raises(ValueError, match="differs"):
        engine.candidate_source_receipt(w, "original_static_fd", bad)
    with pytest.raises(ValueError, match="notLocated"):
        engine.candidate_source_receipt(
            w, "dynamic_tapered_window_in_pinned_tree",
            dict(evidence, source_id="pnas_gitrepo"))
    with pytest.raises(ValueError, match="notLocated"):
        engine.candidate_source_receipt(w, "source_subject_namespace",
                                        dict(evidence, source_id="pnas_static_script"))
    with pytest.raises(ValueError, match="SHA256"):
        engine.candidate_source_receipt(
            w, "original_static_fd", dict(evidence, candidate_sha256="invented"))


def test_author_static_result_requires_nifti_atlas_and_effective_workspace():
    w = world()
    claims = {x["consumer"]: x for x in engine.claim_status(w)}
    static = claims["c_static_reproduction"]
    assert static["state"] == "acquisition_blocked"
    assert {"original_preprocessed_voxel_nifti",
            "original_schaefer_extended_mask",
            "effective_static_gfc_workspace"} <= set(static["missing"])
    assert engine.hypothetical_plan(
        w, "c_public_mat_reproduces_original_static")["status"] == "no_declared_source_route"
    artifact = next(x for x in w["artifacts"]
                    if x["id"] == "original_static_nifti_and_mask_in_pinned_tree")
    assert artifact["status"] == "knownAbsent"
    assert "b35701d" in artifact["scope"]
    assert "negative_search_receipt" in artifact


def test_pareto_needs_source_object_coverage_not_only_consumer_overlap():
    w = world()
    actions = {x["id"]: x for x in engine.action_candidates(w)}
    qc = actions["a_original_motion_primary"]
    code = actions["h_effective_static_code"]
    assert set(qc["potential_consumer_ids"]) >= set(code["potential_consumer_ids"])
    assert not set(qc["potential_artifacts"]) >= set(code["potential_artifacts"])
    assert qc["pareto"] and code["pareto"]
    # All closures still depend on producing the underlying evidence.
    assert code["promotion_authorised"] is False


def test_original_static_is_not_blocked_by_unrelated_parcelled_mat_copy():
    w = world()
    original = next(x for x in w["claims"] if x["id"] == "c_static_reproduction")
    replay = next(x for x in w["actions"] if x["id"] == "d_replay_static")
    assert "source_local_bytes" not in original["requires"]
    assert "source_local_bytes" not in replay["needs"]
    assert "original_preprocessed_voxel_nifti" in original["requires"]
    assert engine.hypothetical_plan(w, "c_static_reproduction")["hypothetical_actions"] == [
        "a_original_motion_primary", "b_rights_review",
        "g_voxel_and_atlas_source", "h_effective_static_code", "d_replay_static"]


def test_known_absent_same_tree_artifact_cannot_be_claimed_as_acquired():
    w = world()
    next(x for x in w["actions"] if x["id"] == "h_effective_static_code")["targets"].append(
        "original_static_nifti_and_mask_in_pinned_tree")
    with pytest.raises(ValueError, match="Scoped knownAbsent"):
        engine.validate_world(w)


def test_scoped_absence_does_not_count_as_live_search_consumer():
    w = world()
    claim = {c["consumer"]: c for c in engine.claim_status(w)}
    assert claim["c_public_mat_reproduces_original_static"]["state"] == "source_scope_blocked"
    assert claim["c_dynamic_replay_from_tree_alone"]["state"] == "source_scope_blocked"
    assert claim["c_static_reproduction"]["state"] == "acquisition_blocked"
    assert claim["c_public_mat_reproduces_original_static"][
        "known_absent_in_declared_source_scope"] == [
            "original_static_nifti_and_mask_in_pinned_tree"]
    for action in engine.action_candidates(w):
        assert "c_public_mat_reproduces_original_static" not in action[
            "potential_consumer_ids"]
        assert "c_dynamic_replay_from_tree_alone" not in action[
            "potential_consumer_ids"]




def test_source_commit_tree_and_blob_identifiers_are_distinct():
    w = world()
    tree = w["observed_git_tree"]
    assert tree["source_commit"] == "b35701d88d904e2f602164ff2eae0fc879772078"
    assert tree["source_tree_sha1"] == "38bdb12d180303f1738b7c5b6d99f34f157c26f9"
    assert tree["source_commit"] != tree["source_tree_sha1"]
    assert len(tree["files"]) == 56
    altered = copy.deepcopy(w)
    altered["observed_git_tree"]["source_tree_sha1"] = altered["observed_git_tree"]["source_commit"]
    with pytest.raises(ValueError, match="diverges|conflated"):
        engine.validate_world(altered)
