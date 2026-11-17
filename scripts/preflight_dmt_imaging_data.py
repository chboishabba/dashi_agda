#!/usr/bin/env python3
"""Fail-closed source-locked DMT imaging file preflight, NOT data replay.

Timmermann et al., PNAS 2023, DOI 10.1073/pnas.2218949120.
No participant data included. File checks do not recompute EEG/fMRI metrics.
"""
import argparse
import hashlib
import json
import re
from pathlib import Path

SOURCE_REPO = "timmer500/DMT_Imaging"
SOURCE_COMMIT = "b35701d88d904e2f602164ff2eae0fc879772078"


def check_manifest(root, manifest_path, source_receipt_path=None):
    errors = []
    if root is None or not root.is_dir():
        errors.append("Data root not supplied or unreadable")
    if manifest_path is None or not manifest_path.is_file():
        errors.append("No locked participant/session manifest")
    if errors:
        return {"status": "blocked", "errors": errors,
                "source_repo": SOURCE_REPO, "source_commit": SOURCE_COMMIT,
                "human_data_replayed": False}
    try:
        manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    except (OSError, ValueError) as exc:
        return {"status": "blocked", "errors": ["Invalid manifest: " + str(exc)],
                "human_data_replayed": False}
    if source_receipt_path is None:
        source_receipt_path = (Path(__file__).resolve().parents[1]
                               / "Docs/receipts/DMTImagingPinnedSourceTree20261024.json")
    try:
        source = json.loads(source_receipt_path.read_text(encoding="utf-8"))
        source_files = {row["path"]: row for row in source["files"]}
        if (source.get("source_repository") != SOURCE_REPO
                or source.get("source_commit") != SOURCE_COMMIT
                or len(source_files) != source["inventory"]["file_count"]
                or source["inventory"]["fmri_file_count"] != 40
                or source["inventory"]["fmri_subjects_with_two_conditions"] != 20):
            errors.append("Source-tree receipt identity/shape mismatch")
    except (OSError, ValueError, KeyError, TypeError):
        source_files = {}
        errors.append("Missing or invalid source-tree receipt")
    if manifest.get("source_repo") != SOURCE_REPO:
        errors.append("Source repository identity mismatch")
    if manifest.get("source_commit") != SOURCE_COMMIT:
        errors.append("Source commit differs from reviewed revision")
    if not manifest.get("permission_reference"):
        errors.append("No explicit reuse permission or rights-review reference")
    entries = manifest.get("files")
    if not isinstance(entries, list) or not entries:
        errors.append("No participant/session files declared")
        entries = []
    identities = set()
    subjects = set()
    splits = {}
    for e in entries:
        if not isinstance(e, dict):
            errors.append("Malformed file entry")
            continue
        sub, sess = str(e.get("subject_id") or ""), str(e.get("session_id") or "")
        relative = e.get("relative_path")
        condition, split, digest = e.get("condition"), e.get("split"), e.get("sha256")
        if not sub or not sess or not isinstance(relative, str) or not relative:
            errors.append("Missing subject/session/path identity")
            continue
        subjects.add(sub)
        if condition not in ("DMT", "placebo"):
            errors.append(sub + ": condition not DMT/placebo")
        if split not in ("train", "test"):
            errors.append(sub + ": split not train/test")
        ident = (sub, sess, condition)
        if ident in identities:
            errors.append("Duplicate participant/session/condition " + repr(ident))
        identities.add(ident)
        splits.setdefault(sub, set()).add(split)
        try:
            local = Path(relative)
            if local.is_absolute() or ".." in local.parts:
                raise ValueError("Path escapes data root")
            candidate = root / local
            if not candidate.is_file() or not candidate.resolve().is_relative_to(root.resolve()):
                raise ValueError("Missing file or path escapes root")
            if not isinstance(digest, str) or len(digest) != 64:
                raise ValueError("Missing SHA256")
            match = re.fullmatch(r"fMRI/Long(S[0-9]+)(DMT|PCB)[.]mat", relative)
            if match is None:
                raise ValueError("Not an individually identified source fMRI file")
            if sub != match.group(1) or condition != (
                "DMT" if match.group(2) == "DMT" else "placebo"
            ):
                raise ValueError("Subject/condition disagrees with filename")
            source_row = source_files.get(relative)
            if source_row is None:
                raise ValueError("File absent from pinned Git source inventory")
            data = candidate.read_bytes()
            if len(data) != source_row.get("size_bytes"):
                raise ValueError("Source byte length mismatch")
            actual = hashlib.sha256(data).hexdigest()
            if actual.lower() != digest.lower():
                raise ValueError("SHA256 mismatch")
            source_blob_sha1 = hashlib.sha1(
                b"blob " + str(len(data)).encode("ascii") + b"\0" + data
            ).hexdigest()
            if source_blob_sha1 != source_row.get("git_blob_sha1"):
                raise ValueError("Pinned Git blob SHA1 mismatch")
        except (OSError, ValueError) as exc:
            errors.append(sub + "/" + sess + ": " + str(exc))
    if any(len(x) > 1 for x in splits.values()):
        errors.append("Participant appears in both train and test")
    return {
        "status": "blocked" if errors else "admissible_manifest_only",
        "errors": errors, "source_repo": SOURCE_REPO,
        "source_commit": SOURCE_COMMIT,
        "declared_subjects": len(subjects),
        "verified_files": len(entries) if not errors else 0,
        "git_source_blob_checks_passed": not errors,
        "human_data_replayed": False,
        "paper_metrics_independently_recomputed": False,
        "scope": "Admission checks only; neither rights adjudication nor published-metric replay",
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--data-root", type=Path)
    parser.add_argument("--manifest", type=Path)
    parser.add_argument("--source-receipt", type=Path)
    args = parser.parse_args()
    result = check_manifest(args.data_root, args.manifest, args.source_receipt)
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0 if result["status"] == "admissible_manifest_only" else 2


if __name__ == "__main__":
    raise SystemExit(main())
