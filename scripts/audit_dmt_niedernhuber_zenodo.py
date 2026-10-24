#!/usr/bin/env python3
"""Source-frozen Zenodo EEG listing audit, NOT an experimental reproduction.

Metadata source: Niedernhuber et al. (2026) original journal data statement and
Niedernhuber Zenodo v1 record 18850897. Original authors retain attribution.
No raw EEG is downloaded, interpreted or redistributed. If local data are
supplied, only hash matching is performed under an external rights review.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "Docs/receipts/DMTNiedernhuberZenodoListing20261025.json"
EXPECTED_MANIFEST_GIT_BLOB = "0d9ecaf1e5623ec8a02e76594bba5e068114e4fb"
PAPER = "10.1177/02698811261481062"
VERSION = "10.5281/zenodo.18850897"
HEX_MD5 = re.compile(r"[0-9a-f]{32}\Z")


def git_blob_sha(data: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(data)).encode("ascii") + b"\0" + data).hexdigest()


def load_source(path=MANIFEST, *, check_pinned=True):
    data = Path(path).read_bytes()
    if check_pinned and git_blob_sha(data) != EXPECTED_MANIFEST_GIT_BLOB:
        raise ValueError("Not the pinned author-attributed source listing")
    return json.loads(data)


def validate_source(source):
    if source.get("schema") != "dashi-dmt-niedernhuber-zenodo-source-listing-v1":
        raise ValueError("Unknown source schema")
    if source["source_root"]["paper_doi"] != PAPER:
        raise ValueError("Different primary-study attribution")
    d = source["deposition"]
    if (d["version_doi"] != VERSION or d["version_record_id"] != "18850897"
            or d["listed_file_pair_count"] != 25 or d["listed_file_count"] != 50
            or d["license_status"] != "unresolved_display_blank"):
        raise ValueError("Zenodo version, file cardinality or rights status changed")
    pairs = source["file_pairs"]
    if not isinstance(pairs, list) or len(pairs) != 25:
        raise ValueError("Expected 25 file *pairs*, not 25 verified participants")
    files = {}
    for pair in pairs:
        prefix = pair["file_prefix"]
        if not re.fullmatch(r"[0-9]{4}", prefix) or len(pair["files"]) != 2:
            raise ValueError("Invalid EEG file pair")
        expected = {prefix + "_equalised.set", prefix + "_equalised.fdt"}
        if {f["name"] for f in pair["files"]} != expected:
            raise ValueError("Incomplete .set/.fdt pair")
        for f in pair["files"]:
            if f["name"] in files or not isinstance(f["md5"], str) or not HEX_MD5.fullmatch(f["md5"]):
                raise ValueError("Duplicate file or malformed original MD5")
            files[f["name"]] = f["md5"]
    if len(files) != 50:
        raise ValueError("Incomplete primary record listing")
    if sorted(p["file_prefix"] for p in pairs) != sorted(AUTHOR_PARTICIPANT_IDS):
        raise ValueError("Zenodo listing differs from original authors' stated participant-ID list")
    owner = source.get("original_analysis_code", {})
    if (owner.get("commit") != AUTHOR_CODE_COMMIT or
            owner.get("repository") != "marianiedernhuber/DMT_microstates"):
        raise ValueError("Primary analysis code commit/source changed")
    file_receipts = owner.get("source_files", [])
    if ({x.get("path"): x.get("git_blob_sha1") for x in file_receipts}
            != AUTHOR_FILE_SHA or len(file_receipts) != len(AUTHOR_FILE_SHA)):
        raise ValueError("Original published code identity not fully pinned")
    for k in ("source_code_declares_25_participants",
              "source_code_declares_three_condition_loop", "source_code_g1_export_identified"):
        if source["consumer_ceiling"].get(k) is not True:
            raise ValueError("Original author code statement missing: " + k)
    for k in ("participant_identity_and_arms_verified_from_recording_contents",
              "original_pipeline_dependencies_verified"):
        if source["consumer_ceiling"].get(k) is not False:
            raise ValueError("Unexecuted author analysis misrepresented as reproduced")
    if any(source["consumer_ceiling"].get(k) is not False for k in (
            "local_bytes_verified", "clinical_condition_crosswalk_verified",
            "microstate_label_arrays_verified", "original_transition_reproduced",
            "measured_entity_experience", "independent_conscious_agent_inferred")):
        raise ValueError("Published file listing incorrectly promoted to measured inference")
    return files


def validate_rights_review(receipt, source):
    expected = {"schema", "version_doi", "reviewer_reference", "rights_basis_reference",
                "human_data_approval_reference", "local_integrity_processing_allowed"}
    if not isinstance(receipt, dict) or set(receipt) != expected:
        raise ValueError("Separate externally reviewed human-data receipt required")
    if (receipt["schema"] != "dashi-niedernhuber-human-data-review-v1"
            or receipt["version_doi"] != source["deposition"]["version_doi"]
            or receipt["local_integrity_processing_allowed"] is not True):
        raise ValueError("Rights scope / version mismatch")
    for k in ("reviewer_reference", "rights_basis_reference", "human_data_approval_reference"):
        if not isinstance(receipt[k], str) or not receipt[k].strip() or receipt[k].lower() in {
                "unknown", "none", "unverified", "tbd"}:
            raise ValueError("Human rights/protocol decision not externally documented")
    return True


def verify_local_file_hashes(directory, files):
    directory = Path(directory)
    if not directory.is_dir() or directory.is_symlink():
        raise ValueError("Local study directory missing or symlinked")
    found = {p.name for p in directory.iterdir()}
    if found != set(files):
        raise ValueError("Missing/extra files; refusing ambiguous local source version")
    for name, expected in sorted(files.items()):
        path = directory / name
        if not path.is_file() or path.is_symlink():
            raise ValueError("Not an ordinary source file: " + name)
        digest = hashlib.md5()
        with path.open("rb") as fh:
            for block in iter(lambda: fh.read(1024 * 1024), b""):
                digest.update(block)
        if digest.hexdigest() != expected:
            raise ValueError("Source MD5 mismatch: " + name)
    return len(files)


def audit(source, materialized_dir=None, rights_receipt=None):
    files = validate_source(source)
    if materialized_dir is None and rights_receipt is not None:
        raise ValueError("Receipt alone is not a dataset")
    matched = 0
    if materialized_dir is not None:
        validate_rights_review(rights_receipt, source)
        matched = verify_local_file_hashes(materialized_dir, files)
    return {
        "schema": "dashi-dmt-niedernhuber-zenodo-audit-v1",
        "original_attribution": "Niedernhuber et al., Journal of Psychopharmacology 2026",
        "original_study_doi": PAPER, "original_zenodo_version_doi": VERSION,
        "original_listing_file_pairs": 25, "listed_recording_files": len(files),
        "hash_matched_local_files": matched,
        "rights_and_ethics_externally_verified_by_script": False,
        "original_author_code_declares_prefixes_as_participant_ids": True,
        "participant_and_condition_mapping_independently_replayed": False,
        "original_author_code_commit": AUTHOR_CODE_COMMIT,
        "original_markov_export_identified": "coh.stats(idx).markov.G1",
        "three_arm_condition_crosswalk_located": False,
        "published_microstate_statistic_reproduced": False,
        "phenomenological_motif_or_agent_observation": False,
        "remaining": [
            "Confirm human-data rights and journal record license independently",
            "Pin original analysis code, processing versions, microstate labelling",
            "Recover treatment conditions, participant IDs and within-file timing",
            "Reproduce original statistic using original code and study samples"],
    }


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--materialized-dir", type=Path)
    p.add_argument("--rights-review", type=Path)
    a = p.parse_args()
    source = load_source()
    receipt = json.loads(a.rights_review.read_text()) if a.rights_review else None
    print(json.dumps(audit(source, a.materialized_dir, receipt), indent=2))


if __name__ == "__main__":
    main()
