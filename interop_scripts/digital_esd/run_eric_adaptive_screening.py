#!/usr/bin/env python3
"""Run the Digital-ESD ERIC adaptive-screening pipeline end to end.

This is a thin orchestration layer over the existing stage scripts. It does
not contain screening semantics of its own.

Pipeline:
  P0-parse  raw/deduplicated ERIC metadata -> normalized study metadata
  P0-A      authoritative unresolved/reviewed screening ledger
  P0-B/C    candidate assessment + duplicate/report-family hypotheses
  P0-D/E/F  calibration worklist + diagnostics + non-scalar Pareto queue
  P0-G      authoritative include/probable -> full-text retrieval/handoff

The wrapper verifies denominator/count invariants after each stage.

Important:
  - ERIC metadata/title/abstract parsing is NOT full-text study parsing.
  - candidate assessment is NOT a screening decision.
  - Pareto priority is NOT a screening decision.
  - full-text retrieval/hashing is NOT SourceAuditAdmission.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
from pathlib import Path
from typing import Any


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as fh:
        while True:
            chunk = fh.read(1024 * 1024)
            if not chunk:
                break
            h.update(chunk)
    return h.hexdigest()


def read_json(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"{path}: expected JSON object")
    return value


def count_jsonl(path: Path) -> int:
    with path.open("r", encoding="utf-8") as fh:
        return sum(1 for line in fh if line.strip())


def run(cmd: list[str], cwd: Path) -> None:
    print("+", " ".join(cmd), flush=True)
    subprocess.run(cmd, cwd=cwd, check=True)


def assert_equal(label: str, observed: int, expected: int) -> None:
    if observed != expected:
        raise RuntimeError(
            f"{label}: denominator mismatch observed={observed} expected={expected}"
        )


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument(
        "--input",
        required=True,
        type=Path,
        help="exact deduplicated ERIC JSON/JSONL artifact",
    )
    ap.add_argument(
        "--repo-root",
        type=Path,
        default=Path(__file__).resolve().parents[2],
    )
    ap.add_argument(
        "--out-root",
        type=Path,
        default=Path("artifacts/digital-esd"),
    )
    ap.add_argument("--expected-count", type=int, default=43996)
    ap.add_argument(
        "--decisions",
        type=Path,
        help="optional authoritative screening-decision overlay JSONL",
    )
    ap.add_argument(
        "--retrieved",
        type=Path,
        help="optional retrieved full-text artifact manifest JSONL for P0-G",
    )
    ap.add_argument(
        "--verify-fulltext-files",
        action="store_true",
        help="recompute SHA-256 for every retrieved full-text artifact",
    )
    ap.add_argument("--calibration-per-stratum", type=int, default=25)
    args = ap.parse_args()

    repo = args.repo_root.resolve()
    input_path = args.input.resolve()
    out_root = args.out_root
    if not out_root.is_absolute():
        out_root = repo / out_root

    parsed_dir = out_root / "parsed"
    screening_dir = out_root / "screening"
    adaptive_dir = screening_dir / "adaptive"
    fulltext_dir = out_root / "fulltext"

    parsed = parsed_dir / "eric-parsed-studies.jsonl"
    parsed_manifest = parsed_dir / "eric-parsed-studies-manifest.json"
    ledger = screening_dir / "screening-decisions.jsonl"
    ledger_manifest = screening_dir / "screening-manifest.json"
    assessments = adaptive_dir / "candidate-assessments.jsonl"
    hypotheses = adaptive_dir / "study-family-hypotheses.jsonl"
    fibres = adaptive_dir / "study-family-fibres.jsonl"
    assessment_manifest = adaptive_dir / "assessment-manifest.json"
    calibration = adaptive_dir / "calibration-selection.jsonl"
    estimate = adaptive_dir / "calibration-estimate.json"
    queue = adaptive_dir / "screening-pareto-queue.jsonl"
    pareto_manifest = adaptive_dir / "pareto-manifest.json"
    fulltext_worklist = fulltext_dir / "fulltext-worklist.jsonl"
    fulltext_manifest = fulltext_dir / "fulltext-handoff-manifest.json"

    py = sys.executable

    # P0-parse: actual ERIC bibliographic/title/abstract parsing.
    run(
        [
            py,
            str(repo / "interop_scripts/digital_esd/parse_eric_studies.py"),
            "--input",
            str(input_path),
            "--out",
            str(parsed),
            "--expected-count",
            str(args.expected_count),
        ],
        repo,
    )
    pmanifest = read_json(parsed_manifest)
    parsed_count = int(pmanifest["record_count"])
    assert_equal("parsed ERIC study metadata", parsed_count, args.expected_count)
    assert_equal("parsed JSONL rows", count_jsonl(parsed), parsed_count)

    # P0-A: authoritative screening ledger. Uses parsed study metadata so the
    # title/abstract snapshot is exactly the parsed object used downstream.
    ledger_cmd = [
        py,
        str(repo / "scripts/prepare_digital_esd_screening_ledger.py"),
        "--input",
        str(parsed),
        "--out-dir",
        str(screening_dir),
    ]
    if args.decisions:
        ledger_cmd.extend(["--decisions", str(args.decisions.resolve())])
    run(ledger_cmd, repo)

    lmanifest = read_json(ledger_manifest)
    ledger_count = int(lmanifest["input_record_count"])
    assert_equal("P0-A ledger input", ledger_count, parsed_count)
    assert_equal("P0-A ledger rows", count_jsonl(ledger), parsed_count)
    authoritative_total = sum(
        int(lmanifest[k])
        for k in (
            "include_count",
            "probable_count",
            "exclude_count",
            "unresolved_count",
        )
    )
    assert_equal("P0-A decision partition", authoritative_total, parsed_count)

    # P0-B/C: advisory assessment and family hypotheses.
    run(
        [
            py,
            str(repo / "scripts/assess_digital_esd_screening_candidates.py"),
            "--metadata",
            str(parsed),
            "--ledger",
            str(ledger),
            "--out-dir",
            str(adaptive_dir),
        ],
        repo,
    )
    amanifest = read_json(assessment_manifest)
    assessment_count = int(amanifest["assessment_count"])
    assert_equal("P0-B candidate assessments", assessment_count, parsed_count)
    assert_equal("P0-B candidate assessment rows", count_jsonl(assessments), parsed_count)

    # P0-D/E/F: stratification, bounded calibration diagnostics and Pareto queue.
    run(
        [
            py,
            str(repo / "scripts/select_digital_esd_screening_pareto.py"),
            "--ledger",
            str(ledger),
            "--assessments",
            str(assessments),
            "--fibres",
            str(fibres),
            "--out-dir",
            str(adaptive_dir),
            "--calibration-per-stratum",
            str(args.calibration_per_stratum),
        ],
        repo,
    )
    qmanifest = read_json(pareto_manifest)
    unresolved = int(lmanifest["unresolved_count"])
    queue_count = int(qmanifest["unresolved_queue_count"])
    assert_equal("P0-F unresolved Pareto queue", queue_count, unresolved)
    assert_equal("P0-F queue rows", count_jsonl(queue), unresolved)

    # P0-G: only authoritative include/probable decisions can enter.
    fulltext_cmd = [
        py,
        str(repo / "scripts/prepare_digital_esd_fulltext_handoff.py"),
        "--ledger",
        str(ledger),
        "--out-dir",
        str(fulltext_dir),
    ]
    if args.retrieved:
        fulltext_cmd.extend(["--retrieved", str(args.retrieved.resolve())])
    if args.verify_fulltext_files:
        fulltext_cmd.append("--verify-files")
    run(fulltext_cmd, repo)

    fmanifest = read_json(fulltext_manifest)
    expected_retained = int(lmanifest["include_count"]) + int(
        lmanifest["probable_count"]
    )
    assert_equal(
        "P0-G authoritative retained/probable",
        int(fmanifest["authoritative_retained_or_probable_count"]),
        expected_retained,
    )
    assert_equal("P0-G full-text worklist rows", count_jsonl(fulltext_worklist), expected_retained)

    execution_manifest = {
        "schema": "digital-esd-adaptive-screening-execution-v1",
        "repo_root": str(repo),
        "input_reference": str(input_path),
        "input_sha256": sha256_file(input_path),
        "expected_count": args.expected_count,
        "parsed_metadata_reference": str(parsed),
        "parsed_metadata_sha256": sha256_file(parsed),
        "parsed_record_count": parsed_count,
        "screening_ledger_reference": str(ledger),
        "screening_ledger_sha256": sha256_file(ledger),
        "screening_record_count": ledger_count,
        "candidate_assessment_reference": str(assessments),
        "candidate_assessment_sha256": sha256_file(assessments),
        "candidate_assessment_count": assessment_count,
        "study_family_hypotheses_reference": str(hypotheses),
        "study_family_hypothesis_count": count_jsonl(hypotheses),
        "study_family_fibres_reference": str(fibres),
        "study_family_fibre_count": count_jsonl(fibres),
        "calibration_selection_reference": str(calibration),
        "calibration_selection_count": count_jsonl(calibration),
        "calibration_estimate_reference": str(estimate),
        "pareto_queue_reference": str(queue),
        "pareto_queue_sha256": sha256_file(queue),
        "pareto_queue_count": queue_count,
        "pareto_front_count": int(qmanifest["pareto_front_count"]),
        "fulltext_worklist_reference": str(fulltext_worklist),
        "fulltext_worklist_sha256": sha256_file(fulltext_worklist),
        "fulltext_worklist_count": expected_retained,
        "fulltext_handoff_manifest_reference": str(fulltext_manifest),
        "retrieved_artifact_count": int(fmanifest["retrieved_artifact_count"]),
        "canonical_evidence_preparation_count": int(
            fmanifest["canonical_evidence_preparation_count"]
        ),
        "denominator_integrity": {
            "parsed_equals_expected": parsed_count == args.expected_count,
            "ledger_equals_parsed": ledger_count == parsed_count,
            "assessments_equal_ledger": assessment_count == ledger_count,
            "authoritative_partition_equals_ledger": authoritative_total == ledger_count,
            "unresolved_queue_equals_authoritative_unresolved": queue_count == unresolved,
            "fulltext_worklist_equals_include_plus_probable": True,
        },
        "authority_boundaries": {
            "metadata_parse_creates_screening_decision": False,
            "candidate_assessment_creates_screening_decision": False,
            "study_family_hypothesis_creates_study_identity": False,
            "pareto_priority_creates_screening_decision": False,
            "fulltext_retrieval_creates_source_audit_admission": False,
        },
    }
    execution_manifest["execution_manifest_sha256_without_self_field"] = hashlib.sha256(
        (
            json.dumps(
                execution_manifest,
                ensure_ascii=False,
                sort_keys=True,
                separators=(",", ":"),
            )
            + "\n"
        ).encode("utf-8")
    ).hexdigest()
    execution_manifest_path = out_root / "adaptive-screening-execution-manifest.json"
    execution_manifest_path.write_text(
        json.dumps(execution_manifest, indent=2, ensure_ascii=False, sort_keys=True)
        + "\n",
        encoding="utf-8",
    )

    print("\nDIGITAL_ESD_ADAPTIVE_SCREENING_COMPLETE")
    print(json.dumps(execution_manifest, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
