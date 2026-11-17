#!/usr/bin/env python3
"""Fail-closed original Smith/Filsinger evidence readiness (NOT physical proof).

A content digest is necessary for traceability but cannot authenticate an
instrument, prove Maxwell field calibration, environmental replenishment,
weather causality or Agda kernel validity. Never mark these gates CLOSED.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
from typing import Any

ROLES = {
    "F10": ("original_pins", "geometry_material", "source_current", "field_flux", "ground_return", "signed_terminal_vi"),
    "METER": ("instrument_calibration", "synchronous_port_work", "signed_error_bounds"),
    "F15": ("natural_source_independence", "controller_work", "load_work", "all_storage_return", "full_loss_and_return"),
    "F16": ("preregistered_intervention", "random_assignment", "sham_control", "cloud_rain_outcome", "meteorological_covariates", "replicated_site"),
    "D1": ("agda_source_commit", "pinned_toolchain", "kernel_exit_receipt", "complete_kernel_log"),
}
ALL_ROLES = {role for group in ROLES.values() for role in group}
BAD_EVIDENCE_KINDS = {"simulation", "proxy", "model", "source_derived", "illustration", "claim", "conditional_theorem"}


def _digest(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def _file_under(base: Path, relative: Any) -> Path | None:
    if not isinstance(relative, str) or not relative or relative.startswith("/"):
        return None
    try:
        resolved = (base / relative).resolve(strict=True)
    except (OSError, ValueError):
        return None
    if not resolved.is_file() or not resolved.is_relative_to(base):
        return None
    return resolved


def check(manifest: dict[str, Any], root: Path) -> dict[str, Any]:
    root = root.resolve()
    errors: list[str] = []
    original = manifest.get("original_id")
    if not isinstance(original, str) or not original.strip() or original.lower().startswith(
        ("hypothetical", "toy", "example", "simulated")
    ):
        errors.append("missing or non-original source-specific original_id")
    record_list = manifest.get("records", [])
    if not isinstance(record_list, list):
        record_list = []
        errors.append("records must be a list")
    seen: set[str] = set()
    verified: set[str] = set()
    # A single valid file/hash cannot be relabelled as 24 independent receipts.
    # Multi-channel acquisitions must provide separately hashed, role-specific
    # extracts with a provenance link, rather than counting the identical bytes.
    used_files: dict[Path, str] = {}
    used_digests: dict[str, str] = {}
    for i, record in enumerate(record_list):
        if not isinstance(record, dict):
            errors.append(f"record {i}: not an object")
            continue
        role = record.get("role")
        if role not in ALL_ROLES:
            errors.append(f"record {i}: unknown role")
            continue
        if role in seen:
            errors.append(f"record {i}: duplicate role {role}")
            continue
        seen.add(role)
        if record.get("original_id") != original:
            errors.append(f"record {i}: different original for role {role}")
            continue
        if record.get("kind") in BAD_EVIDENCE_KINDS or record.get("kind") not in {
            "raw_measurement", "independent_certificate", "pinned_kernel_receipt", "instrument_document"
        }:
            errors.append(f"record {i}: non-original or unrecognised evidence for {role}")
            continue
        if not isinstance(record.get("producer"), str) or not record["producer"].strip():
            errors.append(f"record {i}: missing named evidence producer")
            continue
        if not isinstance(record.get("clock_id"), str) or not record["clock_id"].strip():
            errors.append(f"record {i}: missing clock/sampling reference")
            continue
        path = _file_under(root, record.get("file"))
        if path is None:
            errors.append(f"record {i}: missing or outside-tree original raw file")
            continue
        supplied = record.get("sha256")
        if not isinstance(supplied, str) or len(supplied) != 64 or supplied.lower() != _digest(path):
            errors.append(f"record {i}: hash mismatch or absent hash for {role}")
            continue
        if path in used_files:
            errors.append(f"record {i}: same evidence file re-used for {used_files[path]} and {role}")
            continue
        if supplied.lower() in used_digests:
            errors.append(f"record {i}: identical evidence bytes re-labelled for {used_digests[supplied.lower()]} and {role}")
            continue
        used_files[path] = role
        used_digests[supplied.lower()] = role
        verified.add(role)
    gates: dict[str, Any] = {}
    for gate, roles in ROLES.items():
        missing = sorted(set(roles) - verified)
        gates[gate] = {
            "status": "AWAITING_ORIGINAL_EVIDENCE" if missing else "READY_FOR_INDEPENDENT_REVIEW_NOT_CLOSED",
            "missing_roles": missing,
            "hash_matched_records": len(set(roles) & verified),
            "total_roles": len(roles),
        }
    return {
        "original_id": original,
        "physical_claim_closed": False,
        "kernel_acceptance_established": False,
        "reason": "Raw-file integrity and metadata cannot independently establish Maxwell calibration, source replenishment, causal inference, or Agda kernel acceptance.",
        "gates": gates,
        "errors": errors,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("manifest", type=Path)
    parser.add_argument("--root", type=Path, default=Path.cwd())
    parser.add_argument("--out", type=Path)
    args = parser.parse_args()
    try:
        manifest = json.loads(args.manifest.read_text(encoding="utf-8"))
        if not isinstance(manifest, dict):
            raise ValueError("manifest must be an object")
        receipt = check(manifest, args.root)
    except (ValueError, OSError) as exc:
        print(json.dumps({"error": str(exc), "physical_claim_closed": False, "kernel_acceptance_established": False}))
        return 2
    result = json.dumps(receipt, indent=2, sort_keys=True)
    if args.out:
        args.out.write_text(result + "\n", encoding="utf-8")
    print(result)
    return 1 if receipt["errors"] or any(
        g["status"] == "AWAITING_ORIGINAL_EVIDENCE" for g in receipt["gates"].values()
    ) else 0


if __name__ == "__main__":
    raise SystemExit(main())
