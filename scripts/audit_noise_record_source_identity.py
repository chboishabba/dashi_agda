#!/usr/bin/env python3
"""Fail-closed upstream Noise record identity gate. Not a GPU benchmark.

Original source: qlabs-eng/noise, authors/contributors retained upstream.
DASHI independently audits checkout bytes and a few branch distinctions.
"""
import argparse
import hashlib
import json
from pathlib import Path

PINNED = {
    "train/val/run.py": {
        "git_blob": "000fe5a79252f0a4caf691cb558bf1a362b93930",
        "required": ("Boost -> Cut", "future-token probes", "end merge"),
    },
    "train/speedrun/run.py": {
        "git_blob": "ea8e0945e6bf032ef2faeab8cd938ee0898c0e46",
        "required": ("identity-path", "Cut-lite", "future_draws = key_path_draws = 0",
                     "head_moments", "fused_query", "merge_graph"),
    },
}

def git_blob(data):
    return hashlib.sha1(f"blob {len(data)}\0".encode() + data).hexdigest()

def audit(root):
    records = []
    for path, manifest in PINNED.items():
        file = root / path
        if not file.is_file():
            records.append({"path": path, "status": "MISSING"})
            continue
        data = file.read_bytes()
        blob = git_blob(data)
        missing = [part for part in manifest["required"]
                   if part not in data.decode("utf-8", errors="replace")]
        if blob == manifest["git_blob"] and not missing:
            status = "PASS"
        elif missing:
            status = "UNVERIFIED"
        else:
            status = "CHANGED"
        records.append({
            "path": path, "status": status, "blob": blob,
            "expected_blob": manifest["git_blob"],
            "missing_markers": missing,
            "source_sha256": hashlib.sha256(data).hexdigest(),
        })
    return {
        "records": records,
        "eligible_for_pinned_refinement":
            all(item["status"] == "PASS" for item in records),
    }

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--noise-checkout", type=Path, required=True)
    args = parser.parse_args()
    report = audit(args.noise_checkout)
    print(json.dumps(report, indent=2))
    raise SystemExit(0 if report["eligible_for_pinned_refinement"] else 1)

if __name__ == "__main__":
    main()
