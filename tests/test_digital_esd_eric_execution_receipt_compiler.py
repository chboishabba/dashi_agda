from __future__ import annotations

import hashlib
import json
import subprocess
import sys
from pathlib import Path


SUFFIXES = [
    "real-eric-studies.jsonl",
    "real-eric-studies.manifest.json",
    "screening-decisions.jsonl",
    "screening-manifest.json",
    "candidate-assessments.jsonl",
    "study-family-hypotheses.jsonl",
    "study-family-fibres.jsonl",
    "calibration-selection.jsonl",
    "calibration-estimate.json",
    "screening-pareto-queue.jsonl",
    "pareto-manifest.json",
]


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def test_real_eric_receipt_compiler_reverifies_artifacts_and_emits_agda(tmp_path: Path) -> None:
    artifacts = []
    for i, suffix in enumerate(SUFFIXES):
        path = tmp_path / suffix
        path.write_text(json.dumps({"fixture": i}) + "\n", encoding="utf-8")
        artifacts.append({"path": str(path), "sha256": sha256(path), "size_bytes": path.stat().st_size})

    receipt = {
        "schema": "digital-esd-real-eric-screening-wrapper-receipt-v1",
        "wrapper_version": "digital-esd-real-eric-screening-wrapper-v1",
        "export_root": str(tmp_path / "exports"),
        "started_orchestrating_real_eric_not_synthetic_fixture": True,
        "expected_raw_query_occurrences": 46597,
        "expected_unique_eric_records": 43996,
        "artifacts": artifacts,
        "stops_before_fulltext_acquisition": True,
        "candidate_assessments_create_screening_decisions": False,
        "pareto_queue_creates_screening_decisions": False,
        "creates_source_truth": False,
        "creates_source_audit_admission": False,
    }
    receipt_path = tmp_path / "real-eric-screening-wrapper-receipt.json"
    receipt_path.write_text(json.dumps(receipt), encoding="utf-8")
    output = tmp_path / "Observed.agda"

    subprocess.run(
        [
            sys.executable,
            "interop_scripts/emit_digital_esd_eric_execution_agda.py",
            "--receipt",
            str(receipt_path),
            "--output",
            str(output),
            "--module",
            "DASHI.Generated.TestObservedERIC",
        ],
        check=True,
    )

    text = output.read_text(encoding="utf-8")
    assert "observedRealERICExecution" in text
    assert "Exec.expectedRawQueryOccurrenceCount" in text
    assert "Exec.expectedUniqueERICRecordCount" in text
    assert "true refl" in text
    assert "false refl" in text


def test_real_eric_receipt_compiler_fails_closed_on_artifact_drift(tmp_path: Path) -> None:
    artifacts = []
    for i, suffix in enumerate(SUFFIXES):
        path = tmp_path / suffix
        path.write_text(json.dumps({"fixture": i}) + "\n", encoding="utf-8")
        artifacts.append({"path": str(path), "sha256": sha256(path), "size_bytes": path.stat().st_size})

    artifacts[0]["sha256"] = "0" * 64

    receipt = {
        "wrapper_version": "digital-esd-real-eric-screening-wrapper-v1",
        "export_root": str(tmp_path / "exports"),
        "started_orchestrating_real_eric_not_synthetic_fixture": True,
        "expected_raw_query_occurrences": 46597,
        "expected_unique_eric_records": 43996,
        "artifacts": artifacts,
        "stops_before_fulltext_acquisition": True,
        "candidate_assessments_create_screening_decisions": False,
        "pareto_queue_creates_screening_decisions": False,
        "creates_source_truth": False,
        "creates_source_audit_admission": False,
    }
    receipt_path = tmp_path / "receipt.json"
    receipt_path.write_text(json.dumps(receipt), encoding="utf-8")

    completed = subprocess.run(
        [
            sys.executable,
            "interop_scripts/emit_digital_esd_eric_execution_agda.py",
            "--receipt",
            str(receipt_path),
            "--output",
            str(tmp_path / "Observed.agda"),
        ],
        check=False,
        capture_output=True,
        text=True,
    )
    assert completed.returncode != 0
    assert "artifact digest mismatch" in (completed.stderr + completed.stdout)
