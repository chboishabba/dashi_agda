#!/usr/bin/env python3
"""Source-linked SHA-256 integrity checker for Zhang physical evidence bundles.

One manifest contains one or more paired ON/OFF experimental blocks.
Authenticates BYTES within a trusted local directory, NOT the physical
instrument, author identity, calibration validity, laboratory independence,
statistical observations or unusual gravity. Fail closed for missing artifacts.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path

SHA = re.compile(r"[0-9a-fA-F]{64}\Z")
SOURCE_CLASSES = ("zhang2025_toroid", "zhang2025_HV_sphere")
OBSERVABLES = ("position_m", "theta_rad", "signed_force_N", "signed_torque_Nm")


def required_text(record: dict, key: str) -> str:
    x = record.get(key)
    if not isinstance(x, str) or not x.strip():
        raise ValueError(f"{key}: nonempty field required")
    return x


def hash_file(root: Path, path: str, expected: str) -> dict:
    if not isinstance(path, str) or not path.strip():
        raise ValueError("file name required")
    if not isinstance(expected, str) or not SHA.fullmatch(expected):
        raise ValueError("expected sha256 must be a 64-character hex digest")
    source_root = root.resolve(strict=True)
    candidate = (source_root / path).resolve(strict=True)
    if not candidate.is_relative_to(source_root) or not candidate.is_file():
        raise ValueError("evidence file must be a regular file inside the evidence root")
    h = hashlib.sha256()
    size = 0
    with candidate.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            size += len(chunk)
            h.update(chunk)
    if size == 0:
        raise ValueError("empty evidence file cannot close raw-data payment")
    actual = h.hexdigest()
    if actual.lower() != expected.lower():
        raise ValueError(f"SHA-256 mismatch for {path}")
    return {"relative_path": str(candidate.relative_to(source_root)),
            "sha256": actual, "size_bytes": size}


def inspect_run(root: Path, r: dict) -> dict:
    for key in ("run_id", "lab_id", "apparatus_id", "instrument_id",
                "calibration_revision", "operator_source", "recorded_epoch_utc"):
        required_text(r, key)
    if r.get("source_mode") not in ("ON", "OFF"):
        raise ValueError("exact ON/OFF source mode required")
    raw = hash_file(root, required_text(r, "raw_file"),
                    required_text(r, "raw_sha256"))
    calibration = hash_file(root, required_text(r, "calibration_file"),
                            required_text(r, "calibration_sha256"))
    return {
        "run_id": r["run_id"], "source_mode": r["source_mode"],
        "lab_id": r["lab_id"], "apparatus_id": r["apparatus_id"],
        "instrument_id": r["instrument_id"], "raw": raw,
        "calibration": calibration,
        "recorded_epoch_utc": r["recorded_epoch_utc"],
        "operator_source": r["operator_source"],
    }


def verify_manifest(manifest: dict, evidence_root: Path) -> dict:
    if manifest.get("schema") != "Zhang2025EvidencePacket/v1":
        raise ValueError("unknown evidence packet schema")
    if manifest.get("data_kind") not in ("synthetic", "real_unverified"):
        raise ValueError("do not claim calibrated/replicated authority using data_kind")
    if manifest.get("source_class") not in SOURCE_CLASSES:
        raise ValueError("physical source identity must select exact apparatus class")
    if manifest.get("observable") not in OBSERVABLES:
        raise ValueError("unsupported physical observable")
    protocol = required_text(manifest, "protocol_id")
    regime = required_text(manifest, "declared_regime_fingerprint")
    blocks = manifest.get("blocks")
    if not isinstance(blocks, list) or not blocks:
        raise ValueError("one or more distinct experimental blocks required")
    block_ids = set()
    run_ids = set()
    raw_hashes = set()
    observed = []
    for block in blocks:
        bid = required_text(block, "block_id")
        if bid in block_ids:
            raise ValueError("duplicate experimental block ID")
        block_ids.add(bid)
        pair = block.get("pair")
        if not isinstance(pair, list) or len(pair) != 2:
            raise ValueError("each block must contain exactly one ON/OFF pair")
        if {p.get("source_mode") for p in pair} != {"ON", "OFF"}:
            raise ValueError("each block must have one ON and one OFF run")
        on, off = [next(p for p in pair if p["source_mode"] == mode)
                   for mode in ("ON", "OFF")]
        for field in ("lab_id", "apparatus_id", "instrument_id",
                      "calibration_file", "calibration_sha256",
                      "calibration_revision"):
            if on.get(field) != off.get(field):
                raise ValueError(f"same-apparatus ON/OFF mismatch: {field}")
        if on.get("apparatus_id") != block.get("apparatus_id"):
            raise ValueError("block apparatus does not match source identity")
        if on.get("lab_id") != block.get("lab_id"):
            raise ValueError("block lab does not match source identity")
        checked = [inspect_run(evidence_root, r) for r in pair]
        for read in checked:
            if read["run_id"] in run_ids or read["raw"]["sha256"] in raw_hashes:
                raise ValueError("duplicate run ID or raw evidence across independent runs")
            run_ids.add(read["run_id"])
            raw_hashes.add(read["raw"]["sha256"])
        observed.append({"block_id": bid, "lab_id": on["lab_id"],
                         "apparatus_id": on["apparatus_id"],
                         "on_and_off_byte_integrity_checked": True,
                         "runs": checked})
    distinct_labs = len({b["lab_id"] for b in observed}) > 1
    distinct_rigs = len({b["apparatus_id"] for b in observed}) > 1
    receipt = {
        "schema": manifest["schema"],
        "source_class": manifest["source_class"],
        "protocol_id": protocol,
        "declared_regime_fingerprint": regime,
        "observable": manifest["observable"],
        "data_kind": manifest["data_kind"],
        "verified_block_count": len(observed),
        "byte_integrity_checked": True,
        "distinct_lab_names_declared": distinct_labs,
        "distinct_apparatus_names_declared": distinct_rigs,
        "lab_identity_independently_authenticated": False,
        "calibration_correctness_independently_authenticated": False,
        "physical_replication_established": False,
        "gravity_anomaly_established": False,
        "frames_count_as_independent_trials": False,
        "blocks": observed,
    }
    # Deterministic receipt for ITIR/PNF-style source chaining; this digest
    # hashes a provenance statement, not a physical or identity certification.
    canonical = json.dumps(receipt, sort_keys=True, separators=(",", ":"),
                           ensure_ascii=False).encode("utf-8")
    receipt["verified_manifest_receipt_sha256"] = hashlib.sha256(canonical).hexdigest()
    return receipt


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--evidence-root", type=Path, required=True)
    args = parser.parse_args()
    record = json.loads(args.manifest.read_text(encoding="utf-8"))
    print(json.dumps(verify_manifest(record, args.evidence_root),
                     sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
