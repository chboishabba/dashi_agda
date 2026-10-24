#!/usr/bin/env python3
"""Acquisition-only Git source route for Timmermann et al. DMT EEG/fMRI.

This script does not confer copyright, clinical or re-identification permission.
A reviewed-use reference is mandatory before local file materialisation.
The checkout remains local; never commit or redistribute participant files.
Paper: Timmermann et al., PNAS 2023, DOI 10.1073/pnas.2218949120.
"""
import argparse
import hashlib
import json
import subprocess
from pathlib import Path

SOURCE_COMMIT = "b35701d88d904e2f602164ff2eae0fc879772078"
SOURCE_URL = "https://github.com/timmer500/DMT_Imaging.git"


def verify_checkout(root: Path, receipt: Path) -> dict:
    source = json.loads(receipt.read_text(encoding="utf-8"))
    if (source.get("source_commit") != SOURCE_COMMIT
            or source.get("source_repository") != "timmer500/DMT_Imaging"):
        raise ValueError("Wrong source-tree receipt/revision")
    expected = source["files"]
    if len(expected) != source["inventory"]["file_count"]:
        raise ValueError("Incomplete source-tree receipt")
    for item in expected:
        relative = Path(item["path"])
        if relative.is_absolute() or ".." in relative.parts:
            raise ValueError("Invalid source path")
        path = root / relative
        if not path.is_file() or path.is_symlink():
            raise ValueError("Missing/nonregular source file: " + str(relative))
        raw = path.read_bytes()
        if len(raw) != item["size_bytes"]:
            raise ValueError("Source byte-size mismatch: " + str(relative))
        blob = hashlib.sha1(
            b"blob " + str(len(raw)).encode("ascii") + b"\0" + raw
        ).hexdigest()
        if blob != item["git_blob_sha1"]:
            raise ValueError("Source Git object mismatch: " + str(relative))
    return {
        "status": "git_source_checkout_verified",
        "source_commit": SOURCE_COMMIT,
        "source_files_verified": len(expected),
        "human_analysis_reproduced": False,
        "rights_granted_by_script": False,
        "cohort_exclusions_identified": False,
    }


def acquire(destination: Path, review_record: Path, receipt: Path) -> dict:
    if not review_record.is_file() or not review_record.read_text().strip():
        raise ValueError("A written rights/consent/use review record is required")
    if destination.exists():
        raise ValueError("Destination must not already exist")
    subprocess.run(["git", "clone", "--no-checkout", SOURCE_URL, str(destination)],
                   check=True)
    subprocess.run(["git", "-C", str(destination), "checkout", "--detach",
                    SOURCE_COMMIT], check=True)
    rev = subprocess.check_output(
        ["git", "-C", str(destination), "rev-parse", "HEAD"],
        text=True).strip()
    if rev != SOURCE_COMMIT:
        raise ValueError("Checkout revision mismatch")
    return verify_checkout(destination, receipt)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--destination", type=Path, required=True)
    p.add_argument("--rights-review-record", type=Path, required=True)
    p.add_argument("--source-receipt", type=Path, default=Path(__file__).resolve().parents[1]
                   / "Docs/receipts/DMTImagingPinnedSourceTree20261024.json")
    args = p.parse_args()
    try:
        print(json.dumps(acquire(args.destination, args.rights_review_record,
                                 args.source_receipt), indent=2))
        return 0
    except (ValueError, OSError, subprocess.CalledProcessError) as exc:
        print(json.dumps({"status": "blocked", "reason": str(exc),
                          "human_analysis_reproduced": False}))
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
