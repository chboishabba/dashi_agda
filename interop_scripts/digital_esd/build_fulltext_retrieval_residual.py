#!/usr/bin/env python3
"""Emit the next Digital-ESD full-text retrieval residual from the processing ledger.

Only rows with an authoritative include/probable decision and no verified
full-text artifact are eligible for the retrieval queue.

Metadata-only unresolved rows are *not* retrieval failures and are not queued.
This script does not fetch anything and does not create screening/review truth.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
from pathlib import Path
from typing import Any


def read_jsonl(path: Path) -> list[dict[str, Any]]:
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


def read_tsv(path: Path) -> list[dict[str, str]]:
    with path.open(newline="", encoding="utf-8") as fh:
        return [dict(row) for row in csv.DictReader(fh, delimiter="\t")]


def identity(row: dict[str, Any]) -> str:
    for key in ("source_identity_reference", "sourceIdentityReference", "source_ref"):
        value = row.get(key)
        if isinstance(value, str) and value.strip():
            return value.strip()
    return ""


def sha256_json(value: Any) -> str:
    return hashlib.sha256(
        (json.dumps(value, sort_keys=True, separators=(",", ":")) + "\n").encode("utf-8")
    ).hexdigest()


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--processing-ledger", type=Path, required=True)
    ap.add_argument("--metadata-tsv", type=Path)
    ap.add_argument("--output", type=Path, required=True)
    ap.add_argument("--manifest", type=Path, required=True)
    args = ap.parse_args()

    processing = read_jsonl(args.processing_ledger)
    metadata_by_ref: dict[str, dict[str, str]] = {}
    if args.metadata_tsv:
        for row in read_tsv(args.metadata_tsv):
            ref = identity(row)
            if ref:
                metadata_by_ref[ref] = row

    queue: list[dict[str, Any]] = []
    unresolved_metadata_only = 0

    for row in processing:
        ref = str(row["source_identity_reference"])
        screened = bool(row.get("screened"))
        retained = bool(row.get("retained"))
        verified = bool(row.get("verified"))
        parsed = bool(row.get("parsed"))

        if not screened:
            unresolved_metadata_only += 1
            continue
        if not retained or verified:
            continue

        metadata = metadata_by_ref.get(ref, {})
        candidate_urls = [
            metadata.get(k)
            for k in (
                "url",
                "URL",
                "url_reference",
                "FullTextURL",
                "full_text_url",
                "DownloadURL",
            )
            if metadata.get(k)
        ]
        payload = {
            "source_identity_reference": ref,
            "screening_decision": row.get("screening_decision"),
            "metadata_revision_reference": row.get("metadata_revision_reference"),
            "candidate_urls": candidate_urls,
        }
        queue.append({
            "schema": "digital-esd-fulltext-retrieval-residual-v1",
            "retrieval_residual_reference": "fulltext-retrieval-residual:" + sha256_json(payload),
            **payload,
            "verified_fulltext_observed": verified,
            "parsed_observed": parsed,
            "requires_retrieval_or_resolution": True,
            "candidate_only": True,
            "creates_source_truth": False,
            "creates_reviewed_evidence": False,
            "creates_source_audit_admission": False,
        })

    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open("w", encoding="utf-8") as fh:
        for row in queue:
            fh.write(json.dumps(row, ensure_ascii=False, sort_keys=True) + "\n")

    manifest = {
        "schema": "digital-esd-fulltext-retrieval-residual-manifest-v1",
        "processing_ledger_reference": str(args.processing_ledger),
        "processing_record_count": len(processing),
        "metadata_only_unreviewed_count": unresolved_metadata_only,
        "retained_missing_verified_fulltext_count": len(queue),
        "retrieval_queue_reference": str(args.output),
        "retrieval_queue_sha256": hashlib.sha256(args.output.read_bytes()).hexdigest(),
        "metadata_only_unreviewed_records_are_retrieval_failures": False,
        "retrieval_queue_creates_screening_decision": False,
        "retrieval_queue_creates_source_audit_admission": False,
    }
    args.manifest.parent.mkdir(parents=True, exist_ok=True)
    args.manifest.write_text(
        json.dumps(manifest, indent=2, ensure_ascii=False, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    print(json.dumps(manifest, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
