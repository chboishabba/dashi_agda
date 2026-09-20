#!/usr/bin/env python3
"""Compile a real ERIC wrapper receipt into a concrete Agda execution witness.

This is a receipt compiler only. It does not parse ERIC, screen studies, retrieve
full text, or make review decisions.

Input:
  real-eric-screening-wrapper-receipt.json

Checks:
  - expected_raw_query_occurrences == 46597
  - expected_unique_eric_records == 43996
  - every listed artifact still exists and matches its recorded SHA-256
  - wrapper says it ran real ERIC rather than the synthetic fixture
  - wrapper stops before full-text acquisition
  - wrapper asserts no screening/source-truth/admission promotion

Output:
  an Agda module containing one concrete RealERICStudyExecutionReceipt.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any


EXPECTED_OCCURRENCES = 46597
EXPECTED_UNIQUE = 43996


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def agda_string(value: str) -> str:
    return (
        '"'
        + value.replace("\\", "\\\\").replace('"', '\\"').replace("\n", "\\n")
        + '"'
    )


def load_receipt(path: Path) -> dict[str, Any]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError("wrapper receipt must be an object")
    return payload


def artifact_by_suffix(receipt: dict[str, Any], suffix: str) -> dict[str, Any]:
    matches = [
        row
        for row in receipt.get("artifacts", [])
        if isinstance(row, dict) and str(row.get("path", "")).endswith(suffix)
    ]
    if len(matches) != 1:
        raise ValueError(f"expected exactly one artifact ending with {suffix!r}, got {len(matches)}")
    return matches[0]


def verify_artifact(row: dict[str, Any], receipt_dir: Path) -> tuple[str, str]:
    raw_path = Path(str(row.get("path") or ""))
    candidates = [raw_path]
    if not raw_path.is_absolute():
        candidates.extend([receipt_dir / raw_path, receipt_dir.parent / raw_path])
    path = next((p for p in candidates if p.exists()), None)
    if path is None:
        raise FileNotFoundError(raw_path)
    observed = sha256_file(path)
    expected = str(row.get("sha256") or "").lower()
    if observed != expected:
        raise ValueError(
            f"artifact digest mismatch for {path}: expected={expected} observed={observed}"
        )
    return str(path), observed


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--receipt", type=Path, required=True)
    ap.add_argument(
        "--output",
        type=Path,
        default=Path("artifacts/digital-esd/real-eric-screening/DigitalESDERICStudyExecutionObserved.agda"),
    )
    ap.add_argument(
        "--module",
        default="DASHI.Generated.DigitalESDERICStudyExecutionObserved",
    )
    args = ap.parse_args()

    receipt = load_receipt(args.receipt)
    if int(receipt.get("expected_raw_query_occurrences", -1)) != EXPECTED_OCCURRENCES:
        raise ValueError("wrapper receipt has unexpected raw occurrence count")
    if int(receipt.get("expected_unique_eric_records", -1)) != EXPECTED_UNIQUE:
        raise ValueError("wrapper receipt has unexpected unique ERIC count")
    if receipt.get("started_orchestrating_real_eric_not_synthetic_fixture") is not True:
        raise ValueError("receipt does not identify a real-ERIC run")
    if receipt.get("stops_before_fulltext_acquisition") is not True:
        raise ValueError("receipt does not preserve metadata/full-text boundary")
    for key in (
        "candidate_assessments_create_screening_decisions",
        "pareto_queue_creates_screening_decisions",
        "creates_source_truth",
        "creates_source_audit_admission",
    ):
        if receipt.get(key) is not False:
            raise ValueError(f"receipt promotion firewall is not false: {key}")

    receipt_dir = args.receipt.resolve().parent
    suffixes = {
        "metadata": "real-eric-studies.jsonl",
        "metadata_manifest": "real-eric-studies.manifest.json",
        "ledger": "screening-decisions.jsonl",
        "screening_manifest": "screening-manifest.json",
        "assessments": "candidate-assessments.jsonl",
        "hypotheses": "study-family-hypotheses.jsonl",
        "fibres": "study-family-fibres.jsonl",
        "calibration_selection": "calibration-selection.jsonl",
        "calibration_estimate": "calibration-estimate.json",
        "pareto_queue": "screening-pareto-queue.jsonl",
        "pareto_manifest": "pareto-manifest.json",
    }
    verified: dict[str, tuple[str, str]] = {}
    for name, suffix in suffixes.items():
        verified[name] = verify_artifact(artifact_by_suffix(receipt, suffix), receipt_dir)

    wrapper_version = str(receipt.get("wrapper_version") or "")
    export_root = str(receipt.get("export_root") or "")
    parser_version = "digital-esd-eric-parser-v1"

    def pair(name: str) -> str:
        path, digest = verified[name]
        return f"    {agda_string(path)}\n    {agda_string(digest)}"

    source = f'''module {args.module} where

open import Agda.Builtin.Equality using (refl)

import DASHI.Education.DigitalESDERICStudyExecutionExact as Exec

observedRealERICExecution : Exec.RealERICStudyExecutionReceipt
observedRealERICExecution =
  Exec.real-eric-study-execution-receipt
    {agda_string(wrapper_version)}
    {agda_string(parser_version)}
    {agda_string(export_root)}
    Exec.expectedRawQueryOccurrenceCount
    refl
    Exec.expectedUniqueERICRecordCount
    refl
{pair("metadata")}
{pair("metadata_manifest")}
{pair("ledger")}
{pair("screening_manifest")}
{pair("assessments")}
{pair("hypotheses")}
{pair("fibres")}
{pair("calibration_selection")}
{pair("calibration_estimate")}
{pair("pareto_queue")}
{pair("pareto_manifest")}
    true refl
    true refl
    false refl
    false refl
    false refl
'''

    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(source, encoding="utf-8")
    print(
        json.dumps(
            {
                "schema": "digital-esd-real-eric-agda-receipt-compiler-v1",
                "input_receipt": str(args.receipt),
                "output": str(args.output),
                "expected_occurrences": EXPECTED_OCCURRENCES,
                "expected_unique": EXPECTED_UNIQUE,
                "verified_artifact_count": len(verified),
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
