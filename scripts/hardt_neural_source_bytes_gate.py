#!/usr/bin/env python3
"""Source identity intake for neural/OPM controls: hashes are not biology.

Original experimental credit and permission belong to source custodians.
All analyses produced here are BYTE-IDENTITY ONLY; do not promote to a
reproduced field, genuine sensor, physiological effect, or remote influence.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import math
import re
from pathlib import Path

REQUIRED = ("source_dataset_identifier", "source_author", "source_revision_or_doi",
            "recording_modality", "sampling_hz")
ALLOWED = {"human-OPM-MEG", "human-EEG+OPM-MEG", "human-EEG+SQUID-MEG"}
FILE_KEYS = ("raw_data", "heldout_split_manifest", "control_and_blind_manifest")
SHA = re.compile(r"[a-f0-9]{64}\Z")


def digest(path: Path):
    h = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def _bounded_file(root: Path, name: object) -> Path:
    if not isinstance(name, str) or not name.strip():
        raise ValueError("missing relative original file path")
    q = Path(name)
    if q.is_absolute() or ".." in q.parts:
        raise ValueError("absolute or parent-traversal file path")
    candidate = root / q
    resolved = candidate.resolve(strict=True)
    if not resolved.is_relative_to(root.resolve(strict=True)):
        raise ValueError("source path escapes manifest directory")
    if candidate.is_symlink() or not resolved.is_file() or resolved.stat().st_size == 0:
        raise ValueError("symlink, nonfile, or empty source")
    return resolved


def audit(manifest_path: Path) -> dict:
    manifest_path = manifest_path.resolve(strict=True)
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    if not isinstance(manifest, dict):
        raise ValueError("manifest must be a JSON object")
    if any(not isinstance(manifest.get(k), str) or not manifest[k].strip()
           for k in REQUIRED if k != "sampling_hz"):
        raise ValueError("missing source author/version/modality identity")
    if manifest["recording_modality"] not in ALLOWED:
        raise ValueError("wrong recorded modality for this neural intake")
    f = manifest.get("sampling_hz")
    if isinstance(f, bool) or not isinstance(f, (int, float)) or not math.isfinite(f) or f <= 8:
        raise ValueError("nonfinite or insufficient neural recording Nyquist rate")
    for flag in ("synthetic", "made_up", "invented"):
        if manifest.get("source_origin") == flag:
            raise ValueError("synthetic source cannot be authenticated as experimental")
    root = manifest_path.parent
    outputs = {}
    for key in FILE_KEYS:
        expected = manifest.get(key + "_sha256")
        if not isinstance(expected, str) or not SHA.fullmatch(expected):
            raise ValueError("missing/invalid original SHA256 for " + key)
        p = _bounded_file(root, manifest.get(key + "_file"))
        actual = digest(p)
        if actual != expected:
            raise ValueError("original source byte mismatch: " + key)
        outputs[key] = {"sha256":actual,"size_bytes":p.stat().st_size}
    return {"scope":"local file-byte identity only; no data semantic or sensor validation",
            "source":"user-cited independent original source, not authenticated by checksum alone",
            "source_dataset_identifier":manifest["source_dataset_identifier"],
            "source_revision_or_doi":manifest["source_revision_or_doi"],
            "files":outputs,"three_local_file_hashes_match":True,
            "original_author_or_instrument_identity_authenticated":False,
            "raw_neural_signal_reproduced":False,
            "physical_field_or_remote_influence_verified":False}


def main():
    p = argparse.ArgumentParser()
    p.add_argument("manifest", type=Path)
    args = p.parse_args()
    print(json.dumps(audit(args.manifest), indent=2, sort_keys=True))

if __name__ == "__main__":
    main()
