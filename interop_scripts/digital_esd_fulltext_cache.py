#!/usr/bin/env python3
"""Sparse full-text cache controller for Digital-ESD.

This is intentionally a planner/registry, not a bulk downloader.

Subcommands
-----------
plan
    Select a bounded batch from the authoritative include/probable full-text
    worklist.  Respects item cap, cache byte cap, and free-space reserve.

register
    Register/hash materialised artifacts for a planned batch and produce a
    cache ledger.  Registration does not create review/admission.

gc-plan
    Propose deletion of working copies only when a downstream parse/interop
    receipt has been recorded and revision/digest identity remains in ledger.

status
    Summarise materialised bytes and cache states.

The 43,996-record ERIC metadata universe is never interpreted as a command to
retrieve 43,996 papers.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
from typing import Any


SCHEMA = "digital-esd-sparse-fulltext-cache-v1"


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


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as fh:
        for chunk in iter(lambda: fh.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def gib(value: float) -> int:
    return int(value * 1024 * 1024 * 1024)


def mib(value: float) -> int:
    return int(value * 1024 * 1024)


def source_ref(row: dict[str, Any]) -> str:
    value = str(row.get("source_identity_reference") or "").strip()
    if not value:
        raise ValueError("row missing source_identity_reference")
    return value


def ledger_index(rows: list[dict[str, Any]]) -> dict[str, dict[str, Any]]:
    out: dict[str, dict[str, Any]] = {}
    for row in rows:
        ref = source_ref(row)
        if ref in out:
            raise ValueError(f"duplicate cache ledger entry: {ref}")
        out[ref] = row
    return out


def queue_rank(path: Path | None) -> dict[str, int]:
    if path is None:
        return {}
    ranks: dict[str, int] = {}
    for i, row in enumerate(read_jsonl(path)):
        ranks[source_ref(row)] = i
    return ranks


def current_materialised_bytes(rows: list[dict[str, Any]]) -> int:
    total = 0
    for row in rows:
        state = str(row.get("cache_state") or "")
        if state in {"materialised", "parsedOrReconciled", "evictable"}:
            total += int(row.get("artifact_bytes") or 0)
    return total


def cmd_plan(args: argparse.Namespace) -> int:
    worklist = read_jsonl(args.worklist)
    cache_rows = read_jsonl(args.cache_ledger)
    cache = ledger_index(cache_rows)
    ranks = queue_rank(args.priority_queue)

    args.cache_dir.mkdir(parents=True, exist_ok=True)
    free_bytes = shutil.disk_usage(args.cache_dir).free
    reserve_bytes = gib(args.reserve_gib)
    max_cache_bytes = gib(args.max_cache_gib)
    current_bytes = current_materialised_bytes(cache_rows)

    cache_headroom = max(0, max_cache_bytes - current_bytes)
    free_headroom = max(0, free_bytes - reserve_bytes)
    usable_bytes = min(cache_headroom, free_headroom)

    assumed_bytes = mib(args.assumed_mib_per_item)
    candidates: list[dict[str, Any]] = []
    for original_index, row in enumerate(worklist):
        ref = source_ref(row)
        existing = cache.get(ref)
        if existing and str(existing.get("cache_state")) in {
            "materialised", "parsedOrReconciled", "evictable"
        }:
            continue
        decision = str(row.get("decision") or "")
        if decision not in {"include", "probable"}:
            raise RuntimeError(
                f"{ref}: full-text worklist contains non-retained decision {decision!r}"
            )
        expected = int(row.get("expected_bytes") or assumed_bytes)
        candidates.append({
            **row,
            "_rank": ranks.get(ref, 10**12 + original_index),
            "_expected_bytes": expected,
        })

    candidates.sort(key=lambda row: (row["_rank"], source_ref(row)))

    selected: list[dict[str, Any]] = []
    planned_bytes = 0
    for row in candidates:
        if len(selected) >= args.max_items:
            break
        expected = int(row["_expected_bytes"])
        if planned_bytes + expected > usable_bytes:
            continue
        selected.append(row)
        planned_bytes += expected

    plan_rows = []
    for order, row in enumerate(selected):
        clean = {k: v for k, v in row.items() if not k.startswith("_")}
        ref = source_ref(row)
        plan_rows.append({
            "schema": "digital-esd-fulltext-fetch-plan-v1",
            "batch_order": order,
            "source_identity_reference": ref,
            "screening_decision_reference": clean.get("decision_reference"),
            "decision": clean.get("decision"),
            "fulltext_request_reference": clean.get("fulltext_request_reference"),
            "priority_queue_reference": str(args.priority_queue) if args.priority_queue else None,
            "estimated_bytes": int(row["_expected_bytes"]),
            "cache_dir": str(args.cache_dir),
            "fetch_status": "planned-not-fetched",
            "candidate_only": True,
            "creates_source_truth": False,
            "creates_source_audit_admission": False,
        })

    write_jsonl(args.output, plan_rows)
    manifest = {
        "schema": "digital-esd-fulltext-fetch-plan-manifest-v1",
        "worklist_reference": str(args.worklist),
        "cache_ledger_reference": str(args.cache_ledger) if args.cache_ledger else None,
        "priority_queue_reference": str(args.priority_queue) if args.priority_queue else None,
        "candidate_worklist_count": len(candidates),
        "selected_count": len(plan_rows),
        "planned_estimated_bytes": planned_bytes,
        "planning_assumed_mib_per_item": args.assumed_mib_per_item,
        "current_materialised_bytes": current_bytes,
        "max_cache_bytes": max_cache_bytes,
        "filesystem_free_bytes": free_bytes,
        "required_reserve_bytes": reserve_bytes,
        "usable_planning_bytes": usable_bytes,
        "max_items": args.max_items,
        "all_selected_are_include_or_probable": True,
        "metadata_universe_forces_fulltext_materialisation": False,
        "plan_creates_source_audit_admission": False,
    }
    manifest_path = args.output.with_suffix(".manifest.json")
    manifest_path.write_text(
        json.dumps(manifest, indent=2, ensure_ascii=False, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    print(json.dumps(manifest, sort_keys=True))
    return 0


def cmd_register(args: argparse.Namespace) -> int:
    plan = {source_ref(row): row for row in read_jsonl(args.plan)}
    previous_rows = read_jsonl(args.cache_ledger)
    cache = ledger_index(previous_rows)
    retrieved = read_jsonl(args.retrieved)

    registered = 0
    for row in retrieved:
        ref = source_ref(row)
        if ref not in plan:
            raise RuntimeError(f"{ref}: retrieved artifact is not in the exact fetch plan")
        artifact = Path(str(row.get("artifact_path") or ""))
        if not artifact.exists() or not artifact.is_file():
            raise FileNotFoundError(f"{ref}: {artifact}")

        observed_digest = sha256_file(artifact)
        expected_digest = str(row.get("sha256") or "").lower().removeprefix("sha256:")
        if expected_digest and observed_digest != expected_digest:
            raise RuntimeError(
                f"{ref}: sha256 mismatch expected={expected_digest} observed={observed_digest}"
            )

        size = artifact.stat().st_size
        revision = f"fulltext-sha256:{observed_digest}"
        cache[ref] = {
            "schema": SCHEMA,
            "source_identity_reference": ref,
            "source_revision_reference": revision,
            "artifact_reference": str(artifact),
            "artifact_sha256": observed_digest,
            "artifact_bytes": size,
            "materialised_from_plan_reference": str(args.plan),
            "retrieval_reference": row.get("retrieval_reference"),
            "retrieval_timestamp": row.get("retrieval_timestamp"),
            "parse_or_interop_receipt_reference": None,
            "exact_revision_retained_elsewhere": True,
            "cache_state": "materialised",
            "creates_source_truth": False,
            "creates_source_audit_admission": False,
        }
        registered += 1

    total = current_materialised_bytes(list(cache.values()))
    cap = gib(args.max_cache_gib)
    if total > cap:
        raise RuntimeError(
            f"cache registration would exceed hard cap: {total} > {cap} bytes"
        )

    rows = sorted(cache.values(), key=lambda row: source_ref(row))
    write_jsonl(args.output_ledger, rows)
    manifest = {
        "schema": "digital-esd-fulltext-cache-registration-manifest-v1",
        "registered_count": registered,
        "cache_record_count": len(rows),
        "materialised_bytes": total,
        "hard_cache_cap_bytes": cap,
        "cache_registration_creates_source_truth": False,
        "cache_registration_creates_source_audit_admission": False,
    }
    args.output_ledger.with_suffix(".manifest.json").write_text(
        json.dumps(manifest, indent=2, ensure_ascii=False, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    print(json.dumps(manifest, sort_keys=True))
    return 0


def cmd_gc_plan(args: argparse.Namespace) -> int:
    cache_rows = read_jsonl(args.cache_ledger)
    receipts = {
        source_ref(row): row
        for row in read_jsonl(args.downstream_receipts)
    }
    candidates: list[dict[str, Any]] = []

    for row in cache_rows:
        ref = source_ref(row)
        receipt = receipts.get(ref)
        if receipt is None:
            continue
        if not str(receipt.get("receipt_reference") or receipt.get("invocation_reference") or "").strip():
            continue
        if row.get("exact_revision_retained_elsewhere") is not True:
            continue
        artifact = Path(str(row.get("artifact_reference") or ""))
        candidates.append({
            "source_identity_reference": ref,
            "source_revision_reference": row.get("source_revision_reference"),
            "artifact_reference": str(artifact),
            "artifact_bytes": int(row.get("artifact_bytes") or 0),
            "downstream_receipt_reference": (
                receipt.get("receipt_reference") or receipt.get("invocation_reference")
            ),
            "safe_to_evict_working_copy": True,
            "eviction_creates_source_truth": False,
            "eviction_erases_revision_identity": False,
        })

    candidates.sort(key=lambda row: int(row["artifact_bytes"]), reverse=True)
    target = gib(args.target_gib)
    chosen = []
    total = 0
    for row in candidates:
        if total >= target:
            break
        chosen.append(row)
        total += int(row["artifact_bytes"])

    write_jsonl(args.output, chosen)
    manifest = {
        "schema": "digital-esd-fulltext-gc-plan-v1",
        "eligible_candidate_count": len(candidates),
        "selected_eviction_count": len(chosen),
        "selected_bytes": total,
        "target_bytes": target,
        "performs_deletion": False,
        "requires_downstream_receipt": True,
        "requires_revision_identity_retained_elsewhere": True,
    }
    args.output.with_suffix(".manifest.json").write_text(
        json.dumps(manifest, indent=2, ensure_ascii=False, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    print(json.dumps(manifest, sort_keys=True))
    return 0


def cmd_status(args: argparse.Namespace) -> int:
    rows = read_jsonl(args.cache_ledger)
    counts: dict[str, int] = {}
    for row in rows:
        state = str(row.get("cache_state") or "unknown")
        counts[state] = counts.get(state, 0) + 1
    result = {
        "schema": "digital-esd-fulltext-cache-status-v1",
        "cache_record_count": len(rows),
        "materialised_bytes": current_materialised_bytes(rows),
        "state_counts": dict(sorted(counts.items())),
    }
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser()
    sub = parser.add_subparsers(dest="command_name", required=True)

    plan = sub.add_parser("plan")
    plan.add_argument("--worklist", required=True, type=Path)
    plan.add_argument("--priority-queue", type=Path)
    plan.add_argument("--cache-ledger", type=Path)
    plan.add_argument("--cache-dir", required=True, type=Path)
    plan.add_argument("--output", required=True, type=Path)
    plan.add_argument("--max-items", type=int, default=20)
    plan.add_argument("--max-cache-gib", type=float, default=2.0)
    plan.add_argument("--reserve-gib", type=float, default=5.0)
    plan.add_argument("--assumed-mib-per-item", type=float, default=10.0)
    plan.set_defaults(func=cmd_plan)

    register = sub.add_parser("register")
    register.add_argument("--plan", required=True, type=Path)
    register.add_argument("--retrieved", required=True, type=Path)
    register.add_argument("--cache-ledger", type=Path)
    register.add_argument("--output-ledger", required=True, type=Path)
    register.add_argument("--max-cache-gib", type=float, default=2.0)
    register.set_defaults(func=cmd_register)

    gc = sub.add_parser("gc-plan")
    gc.add_argument("--cache-ledger", required=True, type=Path)
    gc.add_argument("--downstream-receipts", required=True, type=Path)
    gc.add_argument("--output", required=True, type=Path)
    gc.add_argument("--target-gib", type=float, default=1.0)
    gc.set_defaults(func=cmd_gc_plan)

    status = sub.add_parser("status")
    status.add_argument("--cache-ledger", required=True, type=Path)
    status.set_defaults(func=cmd_status)
    return parser


def main() -> int:
    args = build_parser().parse_args()
    if hasattr(args, "max_items") and args.max_items < 1:
        raise SystemExit("--max-items must be >= 1")
    if hasattr(args, "max_cache_gib") and args.max_cache_gib <= 0:
        raise SystemExit("--max-cache-gib must be > 0")
    if hasattr(args, "reserve_gib") and args.reserve_gib < 0:
        raise SystemExit("--reserve-gib must be >= 0")
    return int(args.func(args))


if __name__ == "__main__":
    raise SystemExit(main())
