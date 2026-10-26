#!/usr/bin/env python3
"""Read-only source-identity/MD5 audit for user-provided Zenodo record and EEG files.

Original authors: Niedernhuber et al. (2026), doi:10.1177/02698811261481062;
dataset Zenodo 18850897. A *user-supplied* Zenodo API-shaped JSON record is not
an authenticated live API response, but permits independently testable, exact
50-file metadata joins and checksums of uploaded file bytes. Does not parse EEG
signals, identify subjective motifs, infer agents, or authorize redistribution.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import re
from pathlib import Path

DOI = "10.5281/zenodo.18850897"
SHA_RECORD_EXAMINED = "9fc6a2f48ac0ca501aafe09733968e3b25223ad547f816da440c9cf90a137de0"
PAT = re.compile(r"[0-9]{4}_equalised\.(?:set|fdt)")
MD5 = re.compile(r"[0-9a-f]{32}")


def read_original_record(path):
    payload = Path(path).read_bytes()
    data = json.loads(payload)
    if (str(data.get("id")) != "18850897" or data.get("doi") != DOI
            or data.get("links", {}).get("self") !=
                "https://zenodo.org/api/records/18850897"
            or data.get("metadata", {}).get("license", {}).get("id") != "cc-by-4.0"):
        raise ValueError("Original Zenodo record identity/license does not match")
    files = data.get("files")
    if not isinstance(files, list) or len(files) != 50:
        raise ValueError("Original record has not declared 50 files")
    rows = {}
    for item in files:
        name = item.get("key")
        checksum = item.get("checksum")
        size = item.get("size")
        if (not isinstance(name, str) or not PAT.fullmatch(name)
                or name in rows or not isinstance(checksum, str)
                or not checksum.startswith("md5:")
                or not MD5.fullmatch(checksum[4:])
                or type(size) is not int or size <= 0):
            raise ValueError("Unrecognized/duplicate original deposited file")
        rows[name] = (size, checksum[4:])
    if len(rows) != 50 or len({name[:4] for name in rows}) != 25:
        raise ValueError("Expected 25 actual source pairs")
    for prefix in {name[:4] for name in rows}:
        if {prefix + "_equalised.fdt", prefix + "_equalised.set"} - rows.keys():
            raise ValueError("Missing source EEG pair")
    return rows, hashlib.sha256(payload).hexdigest()


def compare_transcription(record_rows, manifest):
    pairs = manifest.get("file_pairs", [])
    transcribed = {x["name"]: x["md5"] for p in pairs for x in p["files"]}
    if len(transcribed) != 50 or set(transcribed) != set(record_rows):
        raise ValueError("Manifest file names are not an exact source join")
    differences = [name for name in sorted(record_rows)
                   if transcribed[name] != record_rows[name][1]]
    return differences


def verify_uploaded_subset(record_rows, folder):
    folder = Path(folder)
    if not folder.is_dir():
        raise ValueError("Missing uploaded binary download directory")
    entries = []
    for path in sorted(folder.iterdir()):
        name = path.name
        if name.endswith(".bin"):
            name = name[:-4]  # Connector adds .bin to opaque EEGLAB files.
        if not PAT.fullmatch(name):
            continue  # Non-EEG metadata is not processed.
        if name not in record_rows or not path.is_file() or path.is_symlink():
            raise ValueError("Unverified EEG filename or unsafe local file")
        expected_size, expected_md5 = record_rows[name]
        digest = hashlib.md5()
        with path.open("rb") as data:
            for block in iter(lambda: data.read(1024 * 1024), b""):
                digest.update(block)
        got = digest.hexdigest()
        if path.stat().st_size != expected_size or got != expected_md5:
            raise ValueError("Source size/MD5 mismatch: " + name)
        entries.append({"name": name, "bytes": expected_size, "md5_matches": True})
    return entries


def audit(record, manifest, folder=None):
    reference, record_sha = read_original_record(record)
    differences = compare_transcription(reference, json.loads(Path(manifest).read_text()))
    matched = verify_uploaded_subset(reference, folder) if folder is not None else []
    return {
        "schema": "dashi-dmt-zenodo-user-supplied-eeg-byte-audit-v1",
        "original_zenodo_version_doi": DOI,
        "source_record_sha256": record_sha,
        "source_record_matches_examined_upload": record_sha == SHA_RECORD_EXAMINED,
        "user_supplied_record_not_authenticated_live_fetch": True,
        "record_metadata_file_count": len(reference),
        "original_manifest_md5_matches_record": 50 - len(differences),
        "original_manifest_md5_differences": differences,
        "uploaded_file_md5_matched_count": len(matched),
        "uploaded_matched_total_bytes": sum(x["bytes"] for x in matched),
        "uploaded_files": matched,
        "eeg_signal_or_microstate_results_reproduced": False,
        "external_conscious_agents_observed": False,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--record", type=Path, required=True)
    parser.add_argument("--repo-manifest", type=Path, required=True)
    parser.add_argument("--upload-directory", type=Path)
    args = parser.parse_args()
    print(json.dumps(audit(args.record, args.repo_manifest, args.upload_directory),
                     indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
