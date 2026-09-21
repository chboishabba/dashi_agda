#!/usr/bin/env python3
"""Run the Digital-ESD retained-study parser over a large verified corpus.

This is an operational wrapper around the existing thin interop:
  verified full-text index
    -> prepare_slr_source_units.py
    -> deterministic source-unit shards
    -> run_slr_source_unit_parse.py per shard
    -> compile_study_extraction_packets.py per shard
    -> aggregate candidate packets + exact execution manifest

Properties:
- deterministic shard assignment/order;
- resumable: a shard is skipped only when its exact input hash and all output
  hashes still match the shard receipt;
- no parser semantic changes;
- parser output remains candidate-only;
- no extraction coordinate is paid automatically;
- no SourceAuditAdmission is created;
- aggregate counts must reconcile exactly.

The generic SLR parser itself remains the semantic/parser owner.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import hashlib
import json
import os
import shutil
import subprocess
import sys
from pathlib import Path
from typing import Any

HERE = Path(__file__).resolve().parent


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as fh:
        for chunk in iter(lambda: fh.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def read_jsonl(path: Path) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    with path.open("r", encoding="utf-8") as fh:
        for line_no, line in enumerate(fh, 1):
            if not line.strip():
                continue
            row = json.loads(line)
            if not isinstance(row, dict):
                raise ValueError(f"{path}:{line_no}: expected object")
            rows.append(row)
    return rows


def write_jsonl(path: Path, rows: list[dict[str, Any]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as fh:
        for row in rows:
            fh.write(json.dumps(row, ensure_ascii=False, sort_keys=True) + "\n")


def run(cmd: list[str], cwd: Path) -> None:
    completed = subprocess.run(cmd, cwd=cwd, check=False)
    if completed.returncode != 0:
        raise RuntimeError(
            f"command failed with exit={completed.returncode}: "
            + " ".join(cmd)
        )


def receipt_valid(receipt_path: Path, shard_input: Path) -> bool:
    if not receipt_path.is_file() or not shard_input.is_file():
        return False
    try:
        receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
    except Exception:
        return False

    if receipt.get("shard_input_sha256") != sha256_file(shard_input):
        return False

    for key in (
        "parser_manifest_reference",
        "parser_summary_reference",
        "study_packets_reference",
        "resolution_packets_reference",
        "study_parse_summary_reference",
    ):
        p = Path(str(receipt.get(key) or ""))
        if not p.is_file():
            return False
        hash_key = key.removesuffix("_reference") + "_sha256"
        if receipt.get(hash_key) != sha256_file(p):
            return False
    return True


def execute_shard(
    repo_root: Path,
    shard_id: int,
    shard_input: Path,
    shard_dir: Path,
    purpose: str,
) -> dict[str, Any]:
    shard_dir.mkdir(parents=True, exist_ok=True)
    receipt_path = shard_dir / "shard-receipt.json"

    if receipt_valid(receipt_path, shard_input):
        receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
        receipt["resumed"] = True
        return receipt

    records_dir = shard_dir / "slr-records"
    parser_manifest = shard_dir / "slr-parser-manifest.jsonl"
    parser_summary = shard_dir / "slr-parser-summary.json"
    packets_dir = shard_dir / "digital-esd-packets"

    if records_dir.exists():
        shutil.rmtree(records_dir)
    if packets_dir.exists():
        shutil.rmtree(packets_dir)

    run(
        [
            sys.executable,
            str(HERE / "run_slr_source_unit_parse.py"),
            "--repo-root",
            str(repo_root),
            "--input-jsonl",
            str(shard_input),
            "--output-dir",
            str(records_dir),
            "--manifest",
            str(parser_manifest),
            "--summary",
            str(parser_summary),
        ],
        repo_root,
    )

    run(
        [
            sys.executable,
            str(HERE / "compile_study_extraction_packets.py"),
            "--source-units",
            str(shard_input),
            "--parser-manifest",
            str(parser_manifest),
            "--output-dir",
            str(packets_dir),
        ],
        repo_root,
    )

    study_packets = packets_dir / "study-extraction-candidate-packets.jsonl"
    resolution_packets = packets_dir / "screening-resolution-parse-packets.jsonl"
    study_parse_summary = packets_dir / "study-parse-summary.json"

    source_units = read_jsonl(shard_input)
    parser_rows = read_jsonl(parser_manifest)
    study_rows = read_jsonl(study_packets)
    resolution_rows = read_jsonl(resolution_packets)

    expected_packets = len(source_units)
    observed_packets = len(study_rows) + len(resolution_rows)
    if len(parser_rows) != len(source_units):
        raise RuntimeError(
            f"shard {shard_id}: parser manifest/source-unit count mismatch "
            f"{len(parser_rows)} != {len(source_units)}"
        )
    if observed_packets != expected_packets:
        raise RuntimeError(
            f"shard {shard_id}: packet/source-unit count mismatch "
            f"{observed_packets} != {expected_packets}"
        )

    receipt = {
        "schema": "digital-esd-study-parse-shard-receipt-v1",
        "shard_id": shard_id,
        "purpose": purpose,
        "source_unit_count": len(source_units),
        "parser_manifest_count": len(parser_rows),
        "retained_study_packet_count": len(study_rows),
        "screening_resolution_packet_count": len(resolution_rows),
        "shard_input_reference": str(shard_input),
        "shard_input_sha256": sha256_file(shard_input),
        "parser_manifest_reference": str(parser_manifest),
        "parser_manifest_sha256": sha256_file(parser_manifest),
        "parser_summary_reference": str(parser_summary),
        "parser_summary_sha256": sha256_file(parser_summary),
        "study_packets_reference": str(study_packets),
        "study_packets_sha256": sha256_file(study_packets),
        "resolution_packets_reference": str(resolution_packets),
        "resolution_packets_sha256": sha256_file(resolution_packets),
        "study_parse_summary_reference": str(study_parse_summary),
        "study_parse_summary_sha256": sha256_file(study_parse_summary),
        "candidate_only": True,
        "parser_semantics_changed": False,
        "automatic_coordinate_payment": False,
        "source_audit_admission_created": False,
        "resumed": False,
    }
    receipt_path.write_text(
        json.dumps(receipt, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return receipt


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo-root", type=Path, default=Path("."))
    ap.add_argument("--fulltext-index", type=Path, required=True)
    ap.add_argument("--out-dir", type=Path, required=True)
    ap.add_argument(
        "--purpose",
        choices=["retained-study", "screening-resolution"],
        default="retained-study",
    )
    ap.add_argument("--shard-size", type=int, default=128)
    ap.add_argument("--jobs", type=int, default=1)
    ap.add_argument("--max-source-units", type=int)
    args = ap.parse_args()

    if args.shard_size < 1:
        raise SystemExit("--shard-size must be >= 1")
    if args.jobs < 1:
        raise SystemExit("--jobs must be >= 1")

    repo_root = args.repo_root.resolve()
    out = args.out_dir.resolve()
    out.mkdir(parents=True, exist_ok=True)

    prepared = out / "all-source-units.jsonl"
    run(
        [
            sys.executable,
            str(HERE / "prepare_slr_source_units.py"),
            "--fulltext-index",
            str(args.fulltext_index),
            "--output",
            str(prepared),
            "--purpose",
            args.purpose,
        ],
        repo_root,
    )

    all_units = read_jsonl(prepared)
    if args.max_source_units is not None:
        all_units = all_units[: args.max_source_units]

    refs = [str(row["source_unit_ref"]) for row in all_units]
    if refs != sorted(refs):
        all_units.sort(key=lambda row: str(row["source_unit_ref"]))
    if len(set(str(row["source_unit_ref"]) for row in all_units)) != len(all_units):
        raise RuntimeError("duplicate source_unit_ref after preparation")

    shards_root = out / "shards"
    shard_jobs: list[tuple[int, Path, Path]] = []
    for shard_id, start in enumerate(range(0, len(all_units), args.shard_size)):
        rows = all_units[start : start + args.shard_size]
        shard_dir = shards_root / f"{shard_id:06d}"
        shard_input = shard_dir / "source-units.jsonl"
        write_jsonl(shard_input, rows)
        shard_jobs.append((shard_id, shard_input, shard_dir))

    receipts: list[dict[str, Any]] = []
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
        futures = {
            pool.submit(
                execute_shard,
                repo_root,
                shard_id,
                shard_input,
                shard_dir,
                args.purpose,
            ): shard_id
            for shard_id, shard_input, shard_dir in shard_jobs
        }
        for future in concurrent.futures.as_completed(futures):
            receipts.append(future.result())

    receipts.sort(key=lambda r: int(r["shard_id"]))

    aggregate_study: list[dict[str, Any]] = []
    aggregate_resolution: list[dict[str, Any]] = []
    seen_sources: set[str] = set()

    for receipt in receipts:
        for key, sink in (
            ("study_packets_reference", aggregate_study),
            ("resolution_packets_reference", aggregate_resolution),
        ):
            rows = read_jsonl(Path(receipt[key]))
            for row in rows:
                source_ref = str(row["source_identity_reference"])
                if source_ref in seen_sources:
                    raise RuntimeError(
                        f"source emitted more than once across shards: {source_ref}"
                    )
                seen_sources.add(source_ref)
                sink.append(row)

    aggregate_study.sort(key=lambda r: str(r["source_identity_reference"]))
    aggregate_resolution.sort(key=lambda r: str(r["source_identity_reference"]))

    aggregate_dir = out / "aggregate"
    aggregate_dir.mkdir(parents=True, exist_ok=True)
    study_path = aggregate_dir / "study-extraction-candidate-packets.jsonl"
    resolution_path = aggregate_dir / "screening-resolution-parse-packets.jsonl"
    write_jsonl(study_path, aggregate_study)
    write_jsonl(resolution_path, aggregate_resolution)

    parsed_total = len(aggregate_study) + len(aggregate_resolution)
    if parsed_total != len(all_units):
        raise RuntimeError(
            f"aggregate parse count mismatch parsed={parsed_total} "
            f"source_units={len(all_units)}"
        )

    manifest = {
        "schema": "digital-esd-study-parse-corpus-execution-v1",
        "purpose": args.purpose,
        "fulltext_index_reference": str(args.fulltext_index),
        "fulltext_index_sha256": sha256_file(args.fulltext_index),
        "prepared_source_units_reference": str(prepared),
        "prepared_source_units_sha256": sha256_file(prepared),
        "source_unit_count": len(all_units),
        "shard_size": args.shard_size,
        "shard_count": len(receipts),
        "jobs": args.jobs,
        "resumed_shard_count": sum(1 for r in receipts if r.get("resumed")),
        "parsed_source_count": parsed_total,
        "retained_study_packet_count": len(aggregate_study),
        "screening_resolution_packet_count": len(aggregate_resolution),
        "study_packet_reference": str(study_path),
        "study_packet_sha256": sha256_file(study_path),
        "resolution_packet_reference": str(resolution_path),
        "resolution_packet_sha256": sha256_file(resolution_path),
        "all_source_units_parsed_exactly_once": parsed_total == len(all_units),
        "candidate_only": True,
        "parser_semantics_changed": False,
        "automatic_coordinate_payment": False,
        "source_audit_admission_created": False,
        "shard_receipts": [
            str(Path(r["study_parse_summary_reference"]).parent.parent / "shard-receipt.json")
            for r in receipts
        ],
    }
    manifest_path = out / "study-parse-corpus-manifest.json"
    manifest_path.write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )

    print(
        "DIGITAL_ESD_STUDY_PARSE_CORPUS "
        f"purpose={args.purpose} source_units={len(all_units)} "
        f"shards={len(receipts)} parsed={parsed_total} "
        f"study_packets={len(aggregate_study)} "
        f"resolution_packets={len(aggregate_resolution)} "
        f"manifest={manifest_path}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
