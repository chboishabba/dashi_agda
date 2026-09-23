#!/usr/bin/env python3
"""Thin orchestrator for the *real* Digital-ESD ERIC metadata screening path.

This wrapper contains no screening semantics. It invokes the existing owners:

  interop_scripts/digital_esd_eric.py
  scripts/prepare_digital_esd_screening_ledger.py
  scripts/assess_digital_esd_screening_candidates.py
  scripts/select_digital_esd_screening_pareto.py

and records exact command/artifact provenance.

It deliberately stops before full-text acquisition. Full text is requested only
after authoritative include/probable screening decisions exist.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
from datetime import datetime, timezone


WRAPPER_VERSION = "digital-esd-real-eric-screening-wrapper-v1"


def now_iso() -> str:
    return datetime.now(timezone.utc).astimezone().isoformat(timespec="seconds")


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def run_step(name: str, argv: list[str], cwd: Path) -> dict:
    started = now_iso()
    completed = subprocess.run(argv, cwd=str(cwd), check=False)
    finished = now_iso()
    if completed.returncode != 0:
        raise RuntimeError(
            f"{name} failed with exit code {completed.returncode}: {argv}"
        )
    return {
        "name": name,
        "argv": argv,
        "started": started,
        "finished": finished,
        "exit_code": completed.returncode,
        "process_success_creates_screening_decision": False,
        "process_success_creates_source_truth": False,
    }


def artifact(path: Path) -> dict:
    if not path.exists():
        raise FileNotFoundError(path)
    return {
        "path": str(path),
        "sha256": sha256_file(path),
        "size_bytes": path.stat().st_size,
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo-root", type=Path, default=Path("."))
    ap.add_argument("--export-root", type=Path, required=True)
    ap.add_argument(
        "--out-root",
        type=Path,
        default=Path("artifacts/digital-esd/real-eric-screening"),
    )
    ap.add_argument("--expect-occurrences", type=int, default=46597)
    ap.add_argument("--expect-unique", type=int, default=43996)
    ap.add_argument("--calibration-per-stratum", type=int, default=25)
    args = ap.parse_args()

    repo = args.repo_root.resolve()
    export_root = args.export_root
    if not export_root.is_absolute():
        export_root = (repo / export_root).resolve()
    out_root = args.out_root
    if not out_root.is_absolute():
        out_root = (repo / out_root).resolve()
    out_root.mkdir(parents=True, exist_ok=True)

    metadata = out_root / "real-eric-studies.jsonl"
    metadata_manifest = out_root / "real-eric-studies.manifest.json"
    screening_dir = out_root / "screening"
    adaptive_dir = screening_dir / "adaptive"

    steps: list[dict] = []

    steps.append(
        run_step(
            "parse-real-eric",
            [
                sys.executable,
                str(repo / "interop_scripts" / "digital_esd_eric.py"),
                "parse",
                "--export-root",
                str(export_root),
                "--output",
                str(metadata),
                "--manifest",
                str(metadata_manifest),
                "--expect-occurrences",
                str(args.expect_occurrences),
                "--expect-unique",
                str(args.expect_unique),
            ],
            repo,
        )
    )

    steps.append(
        run_step(
            "materialise-unresolved-ledger",
            [
                sys.executable,
                str(repo / "scripts" / "prepare_digital_esd_screening_ledger.py"),
                "--input",
                str(metadata),
                "--out-dir",
                str(screening_dir),
            ],
            repo,
        )
    )

    ledger = screening_dir / "screening-decisions.jsonl"

    steps.append(
        run_step(
            "candidate-assessment-and-family-hypotheses",
            [
                sys.executable,
                str(repo / "scripts" / "assess_digital_esd_screening_candidates.py"),
                "--metadata",
                str(metadata),
                "--ledger",
                str(ledger),
                "--out-dir",
                str(adaptive_dir),
            ],
            repo,
        )
    )

    assessments = adaptive_dir / "candidate-assessments.jsonl"
    fibres = adaptive_dir / "study-family-fibres.jsonl"

    steps.append(
        run_step(
            "calibration-and-pareto-queue",
            [
                sys.executable,
                str(repo / "scripts" / "select_digital_esd_screening_pareto.py"),
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
    )

    outputs = [
        metadata,
        metadata_manifest,
        ledger,
        screening_dir / "screening-manifest.json",
        assessments,
        adaptive_dir / "study-family-hypotheses.jsonl",
        fibres,
        adaptive_dir / "assessment-manifest.json",
        adaptive_dir / "calibration-selection.jsonl",
        adaptive_dir / "calibration-estimate.json",
        adaptive_dir / "screening-pareto-queue.jsonl",
        adaptive_dir / "pareto-manifest.json",
    ]

    manifest = {
        "schema": "digital-esd-real-eric-screening-wrapper-receipt-v1",
        "wrapper_version": WRAPPER_VERSION,
        "repo_root": str(repo),
        "export_root": str(export_root),
        "started_orchestrating_real_eric_not_synthetic_fixture": True,
        "expected_raw_query_occurrences": args.expect_occurrences,
        "expected_unique_eric_records": args.expect_unique,
        "steps": steps,
        "artifacts": [artifact(path) for path in outputs],
        "stops_before_fulltext_acquisition": True,
        "candidate_assessments_create_screening_decisions": False,
        "pareto_queue_creates_screening_decisions": False,
        "creates_source_truth": False,
        "creates_source_audit_admission": False,
        "completed": now_iso(),
    }
    receipt = out_root / "real-eric-screening-wrapper-receipt.json"
    receipt.write_text(
        json.dumps(manifest, indent=2, ensure_ascii=False, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    print(json.dumps(manifest, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
