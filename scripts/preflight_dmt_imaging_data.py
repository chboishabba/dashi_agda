#!/usr/bin/env python3
"""Fail-closed source-locked DMT imaging file preflight, NOT data replay.

Timmermann et al., PNAS 2023, DOI 10.1073/pnas.2218949120.
No participant data included. File checks do not recompute EEG/fMRI metrics.
"""
import argparse
import hashlib
import json
from pathlib import Path

SOURCE_REPO = "timmer500/DMT_Imaging"
SOURCE_COMMIT = "b35701d88d904e2f602164ff2eae0fc879772078"


def check_manifest(root, manifest_path):
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
            with candidate.open("rb") as file:
                actual = hashlib.file_digest(file, "sha256").hexdigest()
            if actual.lower() != digest.lower():
                raise ValueError("SHA256 mismatch")
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
        "human_data_replayed": False,
        "paper_metrics_independently_recomputed": False,
        "scope": "Admission checks only; neither rights adjudication nor published-metric replay",
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--data-root", type=Path)
    parser.add_argument("--manifest", type=Path)
    args = parser.parse_args()
    result = check_manifest(args.data_root, args.manifest)
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0 if result["status"] == "admissible_manifest_only" else 2


if __name__ == "__main__":
    raise SystemExit(main())
