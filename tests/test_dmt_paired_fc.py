"""Only synthetic validation for a DMT paired-FC *candidate*, not EEG/fMRI replay."""
import importlib.util
import sys
import types
from pathlib import Path

import numpy as np
import pytest
from scipy.io import savemat

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location(
    "dmt_paired_fc", ROOT/"scripts/evaluate_dmt_paired_fc.py")
module = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = module
spec.loader.exec_module(module)
static_connectivity = module.static_connectivity
paired_effects = module.paired_effects
load_parcelled_mat = module.load_parcelled_mat
pair_verified_files = module.pair_verified_files


def synthetic(seed, a=0.35, n=6, t=80):
    rng = np.random.default_rng(seed)
    common = rng.normal(size=t)
    return np.vstack([a*common + rng.normal(size=t) for _ in range(n)])


def test_source_convention_diagonal_and_shape():
    x = static_connectivity(synthetic(5), expected_parcels=6)
    assert x.parcels == 6 and x.timepoints == 80
    assert abs(x.mean_fisher_z_including_zero_diagonal -
               x.mean_fisher_z_excluding_diagonal*5/6) < 1e-12


def test_mat_variable_and_bad_arrays(tmp_path):
    matrix = synthetic(8)
    savemat(tmp_path/"x.mat", {"BOLD_AAL": matrix})
    assert load_parcelled_mat(tmp_path/"x.mat").shape == (6, 80)
    with pytest.raises(ValueError):
        load_parcelled_mat(tmp_path/"missing.mat")
    with pytest.raises(ValueError):
        static_connectivity(matrix, expected_parcels=112)
    matrix[0] = 0
    with pytest.raises(ValueError):
        static_connectivity(matrix, expected_parcels=6)


def test_paired_delta_uses_subjects_not_timepoints():
    pairs = {f"S{i}": (synthetic(i, 0.8), synthetic(i+100, 0.1))
             for i in range(1, 7)}
    result = paired_effects(pairs, expected_parcels=6)
    assert result["subjects"] == 6
    assert result["mean_delta"] > 0
    assert result["p_two_sided"] < 0.05
    assert "not_original_paper_replay" in result["status"]


def test_eligibility_cannot_be_inferred_from_file_count():
    manifest = {
        "files": [
            {"subject_id": "S01", "condition": "DMT", "relative_path": "d"},
            {"subject_id": "S01", "condition": "placebo", "relative_path": "p"},
        ],
        "motion_eligible_subjects": ["S01"],
        "motion_exclusion_source_reference": "SYNTHETIC QC ONLY"
    }
    assert pair_verified_files(manifest, ["S01"]) == {
        "S01": {"DMT": "d", "placebo": "p"}}
    for bad in ([], ["S01", "S02"]):
        with pytest.raises(ValueError):
            pair_verified_files(manifest, bad)
    manifest["files"].pop()
    with pytest.raises(ValueError):
        pair_verified_files(manifest, ["S01"])


def test_real_runner_blocks_missing_rights_and_qc_receipt(tmp_path, monkeypatch):
    # Only dependency injection for the fail-closed branch; the separate
    # test_dmt_brainit_consumer_cut covers the true hashed file preflight.
    shim = types.ModuleType("preflight_dmt_imaging_data")
    shim.check_manifest = lambda root, manifest, receipt: {
        "status": "blocked", "errors": ["Missing source/right/quality receipt"]}
    monkeypatch.setitem(sys.modules, "preflight_dmt_imaging_data", shim)
    with pytest.raises(ValueError, match="preflight blocked"):
        module.evaluate_verified_manifest(tmp_path, tmp_path/"missing.json")


def test_source_attribution_and_disclosure():
    text = (ROOT/"scripts/evaluate_dmt_paired_fc.py").read_text()
    assert "10.1073/pnas.2218949120" in text
    assert "preflight_dmt_imaging_data" in text
    assert "full_preprocessing_reproduction" in text
    assert "subjective_qualia_or_entity_identification" in text

def test_original_pnas_static_window_is_eight_minutes_after_injection():
    t = np.arange(840, dtype=np.float64)
    matrix = np.vstack([t, t + 1, t + 2, t + 3, t + 4, t + 5])
    window = module.declared_static_window(matrix)
    assert window.shape == (6, 240)
    assert window[0, 0] == 240
    assert window[0, -1] == 479
    with pytest.raises(ValueError):
        module.declared_static_window(matrix[:, :450])
    assert module.PUBLISHED_STATIC_GFC["eligible_subject_count"] == 16
    assert module.ORIGINAL_DYNAMIC_ELIGIBLE_N == 13
    assert module.PUBLIC_REPO_README_SURVIVED_MOTION_N == 15
    assert module.ORIGINAL_JOINT_EEG_FMRI_N == 12


def test_pnas_aggregate_arithmetic_is_consistent_but_not_reproduced():
    audit_spec = importlib.util.spec_from_file_location(
        "dmt_gfc_published_audit", ROOT / "scripts/audit_dmt_pnas2023_published_gfc.py")
    published = importlib.util.module_from_spec(audit_spec)
    audit_spec.loader.exec_module(published)
    audited = published.audit()
    assert audited["implied_n"] == 16
    assert round(audited["verified_p_two_sided"], 3) == 0.007
    assert audited["status"] == "published_aggregate_arithmetic_consistent"
    assert audited["same_paper_result_reproduced"] is False
    assert audited["participant_ids_recovered"] is False


def test_original_static_cohort_policy_rejects_15_even_with_fake_gate(tmp_path, monkeypatch):
    shim = types.ModuleType("preflight_dmt_imaging_data")
    shim.check_manifest = lambda root, manifest, receipt: {
        "status": "admissible_manifest_only", "source_commit": "SYNTHETIC",
        "source_repo": "SYNTHETIC", "git_source_blob_checks_passed": True}
    monkeypatch.setitem(sys.modules, "preflight_dmt_imaging_data", shim)
    manifest = {
        "analysis": module.EXPLORATORY_PARCELLED_ANALYSIS,
        "input_representation": "BOLD_AAL_MAT",
        "source_metric_relationship": "exploratory_not_source_equivalent",
        "motion_eligible_subjects": [f"S{i:02d}" for i in range(1, 16)],
        "motion_exclusion_source_reference": "SYNTHETIC QC ONLY",
        "alignment_preprocessing_source_reference": "SYNTHETIC ALIGNMENT ONLY",
    }
    import json
    file = tmp_path / "manifest.json"
    file.write_text(json.dumps(manifest))
    with pytest.raises(ValueError, match="16-person"):
        module.evaluate_verified_manifest(tmp_path, file)


def test_real_label_cannot_be_forged_by_parcelled_mat(tmp_path, monkeypatch):
    shim = types.ModuleType("preflight_dmt_imaging_data")
    shim.check_manifest = lambda root, manifest, receipt: {
        "status": "admissible_manifest_only", "source_commit": "SYNTHETIC",
        "source_repo": "SYNTHETIC", "git_source_blob_checks_passed": True}
    monkeypatch.setitem(sys.modules, "preflight_dmt_imaging_data", shim)
    import json
    fake = {
        "analysis": "original_static_gfc",
        "motion_eligible_subjects": sorted(module.PUBLISHED_STATIC_GFC.get(
            "eligible_subject_count", 16) * ["S01"]),
        "motion_exclusion_source_reference": "synthetic",
        "alignment_preprocessing_source_reference": "synthetic",
    }
    file = tmp_path / "fake.json"
    file.write_text(json.dumps(fake))
    with pytest.raises(ValueError, match="voxelwise preprocessed NIfTI"):
        module.evaluate_verified_manifest(tmp_path, file)


def test_parcelled_candidate_requires_explicit_non_equivalence(tmp_path, monkeypatch):
    shim = types.ModuleType("preflight_dmt_imaging_data")
    shim.check_manifest = lambda root, manifest, receipt: {
        "status": "admissible_manifest_only", "source_commit": "SYNTHETIC",
        "source_repo": "SYNTHETIC", "git_source_blob_checks_passed": True}
    monkeypatch.setitem(sys.modules, "preflight_dmt_imaging_data", shim)
    import json
    fake = {"analysis": module.EXPLORATORY_PARCELLED_ANALYSIS,
            "motion_eligible_subjects": ["S01"] * 16,
            "motion_exclusion_source_reference": "synthetic",
            "alignment_preprocessing_source_reference": "synthetic"}
    file = tmp_path / "fake.json"
    file.write_text(json.dumps(fake))
    with pytest.raises(ValueError, match="released parcelled"):
        module.evaluate_verified_manifest(tmp_path, file)
    fake["input_representation"] = "BOLD_AAL_MAT"
    file.write_text(json.dumps(fake))
    with pytest.raises(ValueError, match="Source equivalence not established"):
        module.evaluate_verified_manifest(tmp_path, file)
