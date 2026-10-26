"""Contract tests for the DMT/Brain-IT cross-lane cut.

These check *synthetic* arithmetic and source wording, not Agda typechecking,
participant consent, downloaded dataset integrity, or clinical observations.
"""
from pathlib import Path
import hashlib
import importlib.util
import json

ROOT = Path(__file__).resolve().parents[1]


def load_script(path):
    spec = importlib.util.spec_from_file_location("dmt_cut", ROOT / path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def test_perfect_stimulus_decoder_does_not_identify_secret():
    m = load_script("scripts/audit_brainit_dmt_consumer.py")
    receipt = m.audit()
    assert receipt["perfect_viewed_stimulus_reconstruction"] == "1"
    assert set(receipt["all_stimulus_only_secret_decoder_scores"].values()) == {"1/2"}
    assert receipt["secret_given_stimulus_independence"] is True
    assert receipt["secret_reconstruction_when_ordinary_target_leaks"] == "1"
    assert receipt["conscious_agents_independently_identified"] is False


def test_reuses_canonical_consumer_theorem_without_unmerged_brainit_import():
    src = (ROOT / "DASHI/Cognition/ConsciousRealismDMTBrainITConsumerExact.agda").read_text()
    assert "Fabric.consumerCannotFactorThroughProjection" in src
    assert "noUniversalConcealedTargetFromStimulus" in src
    assert "noUniversalOriginDecoderFromSharedLaw" in src
    assert "2510.25976v2" in src
    assert "10.1073/pnas.2218949120" in src
    assert "import DASHI.Biology.BrainIT" not in src
    aggregate = (ROOT / "DASHI/Cognition/ConsciousRealismDMTEverything.agda").read_text()
    assert "ConsciousRealismDMTBrainITConsumerExact" in aggregate
    cognition = (ROOT / "DASHI/Cognition/Everything.agda").read_text()
    assert "ConsciousRealismDMTEverything" in cognition
    kluver = (ROOT / "DASHI/Cognition/KluverLogPolar5HT2AEverything.agda").read_text()
    assert "ConsciousRealismDMTIdentifiabilityExact" not in kluver


def test_data_intake_refuses_unverified_dataset_and_missing_rights(tmp_path):
    m = load_script("scripts/preflight_dmt_imaging_data.py")
    assert m.check_manifest(None, None)["status"] == "blocked"

    # Invented 40-file Git source inventory, NOT the downloaded public data.
    # Exercise actual Git-blob hashing and the subject/condition firewall.
    payload = b"synthetic unit test bytes (not participant data)"
    rel = "fMRI/LongS01PCB.mat"
    (tmp_path / "fMRI").mkdir()
    (tmp_path / rel).write_bytes(payload)
    blob_sha = hashlib.sha1(
        b"blob " + str(len(payload)).encode("ascii") + b"\0" + payload
    ).hexdigest()
    fake_files = [
        {"path": "fMRI/LongS%02d%s.mat" % (n, cond),
         "size_bytes": len(payload), "git_blob_sha1": "0" * 40}
        for n in range(1, 21) for cond in ("DMT", "PCB")
    ]
    for row in fake_files:
        if row["path"] == rel:
            row["git_blob_sha1"] = blob_sha
    fake_tree = {
        "source_repository": m.SOURCE_REPO, "source_commit": m.SOURCE_COMMIT,
        "inventory": {"file_count": 40,
                      "fmri_file_count": 40,
                      "fmri_subjects_with_two_conditions": 20},
        "files": fake_files,
    }
    receipt = tmp_path / "synthetic_source_tree.json"
    receipt.write_text(json.dumps(fake_tree))
    entry = {
        "subject_id": "S01", "session_id": "one",
        "condition": "placebo", "split": "test",
        "relative_path": rel,
        "sha256": hashlib.sha256(payload).hexdigest(),
    }
    manifest = {
        "source_repo": m.SOURCE_REPO, "source_commit": m.SOURCE_COMMIT,
        "permission_reference": "SYNTHETIC UNIT-TEST ONLY", "files": [entry],
    }
    path = tmp_path / "manifest.json"
    path.write_text(json.dumps(manifest))
    assert m.check_manifest(tmp_path, path, receipt)["status"] == "admissible_manifest_only"

    manifest["permission_reference"] = ""
    path.write_text(json.dumps(manifest))
    assert m.check_manifest(tmp_path, path, receipt)["status"] == "blocked"
    manifest["permission_reference"] = "SYNTHETIC UNIT-TEST ONLY"

    manifest["files"].append({**entry, "session_id": "two", "split": "train"})
    path.write_text(json.dumps(manifest))
    split_error = m.check_manifest(tmp_path, path, receipt)
    assert split_error["status"] == "blocked"
    assert any("both train and test" in x for x in split_error["errors"])

    manifest["files"] = [{**entry, "sha256": "0" * 64}]
    path.write_text(json.dumps(manifest))
    assert m.check_manifest(tmp_path, path, receipt)["status"] == "blocked"

    manifest["files"] = [{**entry, "condition": "DMT"}]
    path.write_text(json.dumps(manifest))
    assert m.check_manifest(tmp_path, path, receipt)["status"] == "blocked"

    fake_files[1]["git_blob_sha1"] = "1" * 40
    # The actual included PCB row must fail its Git source-object check.
    for row in fake_files:
        if row["path"] == rel:
            row["git_blob_sha1"] = "1" * 40
    receipt.write_text(json.dumps(fake_tree))
    manifest["files"] = [entry]
    path.write_text(json.dumps(manifest))
    assert m.check_manifest(tmp_path, path, receipt)["status"] == "blocked"
