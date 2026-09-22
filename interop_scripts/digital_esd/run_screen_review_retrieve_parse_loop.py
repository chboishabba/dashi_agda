#!/usr/bin/env python3
"""Advance the Digital-ESD screening -> retrieval -> parse loop.

Thin dashi_agda orchestration only.  Generic screening/review/full-text gates
remain owned by SLR; scholarly parsing remains owned by the generic SLR parser.

Subcommands:

  prepare-review
      Refresh/create the next bounded review packet batch.

  advance
      Apply an explicit reviewed decision overlay, refresh the adaptive queue,
      rebuild the 43,996-row processing ledger, emit the next full-text
      retrieval residual, optionally retrieve a bounded batch, rebuild the
      full-text gate, and parse newly verified artifacts.

Candidate recommendations are never auto-promoted.
"""

from __future__ import annotations

import argparse
import csv
import json
import os
import subprocess
import sys
from pathlib import Path
from typing import Any


HERE = Path(__file__).resolve().parent
DASHI_ROOT = HERE.parents[1]


def run(cmd: list[str], *, cwd: Path | None = None, allow_codes: set[int] = {0}) -> int:
    print("+", " ".join(cmd), file=sys.stderr)
    completed = subprocess.run(cmd, cwd=str(cwd) if cwd else None, check=False)
    if completed.returncode not in allow_codes:
        raise SystemExit(completed.returncode)
    return completed.returncode


def read_jsonl(path: Path | None) -> list[dict[str, Any]]:
    if path is None or not path.exists():
        return []
    rows: list[dict[str, Any]] = []
    with path.open("r", encoding="utf-8") as fh:
        for n, line in enumerate(fh, 1):
            if not line.strip():
                continue
            row = json.loads(line)
            if not isinstance(row, dict):
                raise ValueError(f"{path}:{n}: expected object")
            rows.append(row)
    return rows


def write_jsonl(path: Path, rows: list[dict[str, Any]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as fh:
        for row in rows:
            fh.write(json.dumps(row, ensure_ascii=False, sort_keys=True) + "\n")


def read_tsv(path: Path) -> list[dict[str, str]]:
    with path.open(newline="", encoding="utf-8") as fh:
        return [dict(row) for row in csv.DictReader(fh, delimiter="\t")]


def resolve_slr_root(explicit: Path | None) -> Path:
    if explicit:
        root = explicit.resolve()
    elif os.environ.get("SLR_REPO_ROOT"):
        root = Path(os.environ["SLR_REPO_ROOT"]).resolve()
    else:
        root = (DASHI_ROOT.parent / "slr").resolve()
    required = [
        root / "scripts" / "prepare_digital_esd_review_packets.py",
        root / "scripts" / "apply_digital_esd_screening_decisions.py",
        root / "scripts" / "refresh_digital_esd_review_queue.py",
        root / "scripts" / "prepare_digital_esd_fulltext_index.py",
    ]
    missing = [str(p) for p in required if not p.exists()]
    if missing:
        raise FileNotFoundError("missing SLR helpers: " + ", ".join(missing))
    return root


def authoritative_ledger(root: Path) -> Path:
    reviewed = root / "screening_ledger_reviewed.tsv"
    base = root / "screening_ledger.tsv"
    if reviewed.exists():
        return reviewed
    if base.exists():
        return base
    raise FileNotFoundError(f"no screening ledger under {root}")


def prepare_review(
    *,
    slr_root: Path,
    artifact_root: Path,
    max_packets: int,
    selection: str,
) -> Path:
    script = slr_root / "scripts" / "prepare_digital_esd_review_packets.py"
    review_dir = artifact_root / "review"
    run([
        sys.executable, str(script),
        "--artifact-dir", str(artifact_root),
        "--output-dir", str(review_dir),
        "--max-packets", str(max_packets),
        "--selection", selection,
    ], cwd=slr_root)
    return review_dir / "review_packets.jsonl"


def merge_retrieved_manifests(
    existing: Path | None,
    new: Path,
    output: Path,
) -> int:
    by_ref: dict[str, dict[str, Any]] = {}
    for source in [existing, new]:
        for row in read_jsonl(source):
            ref = str(row.get("source_identity_reference") or "").strip()
            if not ref:
                raise ValueError(f"{source}: retrieved row lacks source identity")
            by_ref[ref] = row
    rows = [by_ref[k] for k in sorted(by_ref)]
    write_jsonl(output, rows)
    return len(rows)


def merge_retrieval_failures(
    existing: Path | None,
    new: Path,
    output: Path,
) -> int:
    """Keep one latest failed-attempt receipt per source for normal-lane deferral."""
    by_ref: dict[str, dict[str, Any]] = {}
    for source in [existing, new]:
        for row in read_jsonl(source):
            ref = str(row.get("source_identity_reference") or "").strip()
            if not ref:
                continue
            by_ref[ref] = row
    write_jsonl(output, [by_ref[ref] for ref in sorted(by_ref)])
    return len(by_ref)


def write_alternate_resolution_queue(failures: Path, output: Path) -> int:
    """Expose failed public retrievals without returning them to the main queue."""
    rows: list[dict[str, Any]] = []
    for failure in read_jsonl(failures):
        ref = str(failure.get("source_identity_reference") or "").strip()
        if not ref:
            continue
        rows.append({
            "schema": "digital-esd-alternate-fulltext-resolution-v1",
            "source_identity_reference": ref,
            "last_retrieval_failure": failure,
            "requires_alternate_same_object_source": True,
            "candidate_only": True,
            "creates_screening_decision": False,
            "creates_source_truth": False,
            "creates_reviewed_evidence": False,
            "creates_source_audit_admission": False,
        })
    write_jsonl(output, rows)
    return len(rows)


def build_fulltext_index(
    *,
    slr_root: Path,
    ledger: Path,
    artifact_root: Path,
    retrieved_manifest: Path | None,
) -> Path:
    fulltext_dir = artifact_root / "fulltext"
    script = slr_root / "scripts" / "prepare_digital_esd_fulltext_index.py"
    cmd = [
        sys.executable, str(script),
        "--ledger", str(ledger),
        "--output-dir", str(fulltext_dir),
    ]
    if retrieved_manifest and retrieved_manifest.exists():
        cmd += ["--retrieved-manifest", str(retrieved_manifest)]
    run(cmd, cwd=slr_root, allow_codes={0, 2})
    return fulltext_dir / "digital_esd_fulltext_index.tsv"


def build_processing_and_residual(
    *,
    artifact_root: Path,
    ledger: Path,
    fulltext_index: Path,
) -> tuple[Path, Path]:
    parse_dir = artifact_root / "slr-parse"
    parse_dir.mkdir(parents=True, exist_ok=True)
    processing = parse_dir / "study-processing-ledger.jsonl"
    processing_manifest = parse_dir / "study-processing-ledger-manifest.json"

    cmd = [
        sys.executable, str(HERE / "build_processing_ledger.py"),
        "--screening-ledger", str(ledger),
        "--fulltext-index", str(fulltext_index),
        "--output-ledger", str(processing),
        "--output-manifest", str(processing_manifest),
    ]
    optional = [
        ("--materialization-receipts", parse_dir / "materialization-receipts.jsonl"),
        ("--slr-handoff", parse_dir / "slr-handoff-receipts.jsonl"),
        ("--slr-parse-receipts", parse_dir / "slr-parse-receipts.jsonl"),
        ("--slr-review-receipts", parse_dir / "slr-review-receipts.jsonl"),
        ("--source-audit-receipts", parse_dir / "source-audit-receipts.jsonl"),
    ]
    for flag, path in optional:
        if path.exists():
            cmd += [flag, str(path)]
    run(cmd, cwd=DASHI_ROOT)

    residual = parse_dir / "fulltext-retrieval-residual.jsonl"
    residual_manifest = parse_dir / "fulltext-retrieval-residual-manifest.json"
    metadata = artifact_root / "digital_esd_eric_metadata.tsv"
    cmd = [
        sys.executable, str(HERE / "build_fulltext_retrieval_residual.py"),
        "--processing-ledger", str(processing),
        "--output", str(residual),
        "--manifest", str(residual_manifest),
    ]
    if metadata.exists():
        cmd += ["--metadata-tsv", str(metadata)]
    run(cmd, cwd=DASHI_ROOT)
    return processing, residual


def apply_review_and_refresh(
    *,
    slr_root: Path,
    artifact_root: Path,
    decisions: Path,
    max_packets: int,
    selection: str,
) -> Path:
    input_ledger = authoritative_ledger(artifact_root)
    reviewed = artifact_root / "screening_ledger_reviewed.tsv"

    run([
        sys.executable,
        str(slr_root / "scripts" / "apply_digital_esd_screening_decisions.py"),
        "--ledger", str(input_ledger),
        "--decisions", str(decisions),
        "--output", str(reviewed),
        "--manifest", str(artifact_root / "screening_ledger_reviewed.manifest.json"),
    ], cwd=slr_root)

    run([
        sys.executable,
        str(slr_root / "scripts" / "refresh_digital_esd_review_queue.py"),
        "--ledger", str(reviewed),
        "--assessments", str(artifact_root / "candidate_assessments.jsonl"),
        "--hypotheses", str(artifact_root / "study_family_hypotheses.jsonl"),
        "--output-dir", str(artifact_root),
    ], cwd=slr_root)

    prepare_review(
        slr_root=slr_root,
        artifact_root=artifact_root,
        max_packets=max_packets,
        selection=selection,
    )
    return reviewed


def parse_verified(
    *,
    slr_root: Path,
    artifact_root: Path,
    max_items: int | None,
) -> None:
    cmd = [
        sys.executable,
        str(HERE / "run_verified_fulltext_parse.py"),
        "--slr-root", str(slr_root),
        "--artifact-root", str(artifact_root),
    ]
    if max_items is not None:
        cmd += ["--max-items", str(max_items)]
    run(cmd, cwd=DASHI_ROOT)


def cmd_prepare(args: argparse.Namespace) -> int:
    slr_root = resolve_slr_root(args.slr_root)
    artifact_root = args.artifact_root.resolve()
    path = prepare_review(
        slr_root=slr_root,
        artifact_root=artifact_root,
        max_packets=args.max_packets,
        selection=args.selection,
    )
    print(json.dumps({
        "review_packets": str(path),
        "candidate_auto_promoted": False,
    }, sort_keys=True))
    return 0


def cmd_advance(args: argparse.Namespace) -> int:
    slr_root = resolve_slr_root(args.slr_root)
    artifact_root = args.artifact_root.resolve()

    ledger = apply_review_and_refresh(
        slr_root=slr_root,
        artifact_root=artifact_root,
        decisions=args.decisions.resolve(),
        max_packets=args.max_packets,
        selection=args.selection,
    )

    persistent_retrieved = artifact_root / "fulltext" / "retrieved-artifacts.jsonl"
    fulltext_index = build_fulltext_index(
        slr_root=slr_root,
        ledger=ledger,
        artifact_root=artifact_root,
        retrieved_manifest=persistent_retrieved if persistent_retrieved.exists() else None,
    )
    processing, residual = build_processing_and_residual(
        artifact_root=artifact_root,
        ledger=ledger,
        fulltext_index=fulltext_index,
    )

    retrieval_returncode = None
    alternate_resolution_queue = artifact_root / "fulltext" / "alternate-resolution.jsonl"
    if args.fetch_max_items > 0:
        new_manifest = artifact_root / "fulltext" / "retrieved-artifacts.new.jsonl"
        failure_log = artifact_root / "fulltext" / "retrieval-failures.jsonl"
        new_failure_log = artifact_root / "fulltext" / "retrieval-failures.new.jsonl"
        retrieval_returncode = run([
            sys.executable,
            str(HERE / "fetch_retrieval_residual.py"),
            "--residual", str(residual),
            "--cache-dir", str(artifact_root / "fulltext" / "cache"),
            "--output-manifest", str(new_manifest),
            "--failure-log", str(new_failure_log),
            "--prior-failures", str(failure_log),
            "--max-items", str(args.fetch_max_items),
            "--timeout", str(args.fetch_timeout),
            "--max-bytes", str(args.fetch_max_bytes),
        ], cwd=DASHI_ROOT, allow_codes={0, 2})

        if new_manifest.exists():
            merge_retrieved_manifests(
                persistent_retrieved if persistent_retrieved.exists() else None,
                new_manifest,
                persistent_retrieved,
            )
            fulltext_index = build_fulltext_index(
                slr_root=slr_root,
                ledger=ledger,
                artifact_root=artifact_root,
                retrieved_manifest=persistent_retrieved,
            )
            processing, residual = build_processing_and_residual(
                artifact_root=artifact_root,
                ledger=ledger,
                fulltext_index=fulltext_index,
            )

        if new_failure_log.exists():
            merge_retrieval_failures(
                failure_log if failure_log.exists() else None,
                new_failure_log,
                failure_log,
            )
        if failure_log.exists():
            write_alternate_resolution_queue(failure_log, alternate_resolution_queue)

    verified_rows = [
        row for row in read_tsv(fulltext_index)
        if row.get("status") == "verified"
    ]
    if args.parse_verified and verified_rows:
        parse_verified(
            slr_root=slr_root,
            artifact_root=artifact_root,
            max_items=args.parse_max_items,
        )

    summary = {
        "schema": "digital-esd-screen-review-retrieve-parse-loop-v1",
        "authoritative_ledger": str(ledger),
        "processing_ledger": str(processing),
        "retrieval_residual": str(residual),
        "verified_fulltext_count": len(verified_rows),
        "retrieval_transport_returncode": retrieval_returncode,
        "alternate_fulltext_resolution_queue": str(alternate_resolution_queue),
        "next_review_packets": str(artifact_root / "review" / "review_packets.jsonl"),
        "candidate_auto_promoted": False,
        "retrieval_creates_screening_decision": False,
        "parse_creates_reviewed_evidence": False,
        "parse_creates_source_audit_admission": False,
    }
    print(json.dumps(summary, indent=2, sort_keys=True))
    return 0


def main() -> int:
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="command", required=True)

    p = sub.add_parser("prepare-review")
    p.add_argument("--slr-root", type=Path)
    p.add_argument("--artifact-root", type=Path, required=True)
    p.add_argument("--max-packets", type=int, default=50)
    p.add_argument(
        "--selection",
        choices=("calibration-first", "pareto-first"),
        default="calibration-first",
    )
    p.set_defaults(func=cmd_prepare)

    a = sub.add_parser("advance")
    a.add_argument("--slr-root", type=Path)
    a.add_argument("--artifact-root", type=Path, required=True)
    a.add_argument("--decisions", type=Path, required=True)
    a.add_argument("--max-packets", type=int, default=50)
    a.add_argument(
        "--selection",
        choices=("calibration-first", "pareto-first"),
        default="calibration-first",
    )
    a.add_argument("--fetch-max-items", type=int, default=20)
    a.add_argument("--fetch-timeout", type=float, default=30.0)
    a.add_argument("--fetch-max-bytes", type=int, default=100 * 1024 * 1024)
    a.add_argument("--parse-verified", action="store_true")
    a.add_argument("--parse-max-items", type=int)
    a.set_defaults(func=cmd_advance)

    args = ap.parse_args()
    return int(args.func(args))


if __name__ == "__main__":
    raise SystemExit(main())
