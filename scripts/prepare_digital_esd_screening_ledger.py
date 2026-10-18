#!/usr/bin/env python3
"""Compile a durable Digital-ESD title/abstract screening ledger.

This script does NOT decide inclusion by heuristic. It preserves the exact
metadata snapshot for every input record, emits one unresolved receipt per
record by default, and optionally overlays explicit reviewer/model/process
decisions supplied in JSONL.

Expected input:
  artifacts/digital-esd/deduplication/eric-deduplicated-records.json

The input may be either a JSON array or an object containing a records/items
array. Field names are detected conservatively for ERIC-style metadata.

Decision overlay JSONL rows use:
{
  "source_identity_reference": "ERIC:<id>",
  "decision": "include|probable|exclude|unresolved",
  "reason_codes": ["potentiallyRelevant"],
  "free_text_reason": "...",
  "reviewer_or_model_reference": "...",
  "process_reference": "...",
  "decision_timestamp": "...",
  "supersedes_decision_reference": null
}

Outputs:
  screening-decisions.jsonl
  screening-manifest.json

Authority boundary:
  screening != source truth != SourceAuditAdmission.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from datetime import datetime, timezone
from typing import Any

ALLOWED_DECISIONS = {"include", "probable", "exclude", "unresolved"}
ALLOWED_REASON_CODES = {
    "populationMismatch",
    "educationContextMismatch",
    "interventionOrTechnologyMismatch",
    "sustainabilityQuestionMismatch",
    "noEmpiricalStudy",
    "noRelevantReviewOrMethodRole",
    "insufficientTitleAbstractEvidence",
    "inaccessibleAbstract",
    "languageOutsideDeclaredScope",
    "publicationTypeOutsideDeclaredScope",
    "duplicateCandidate",
    "awaitingScreeningReview",
    "potentiallyRelevant",
    "requiresFullText",
    "otherScreeningReason",
}


def now_iso() -> str:
    return datetime.now(timezone.utc).astimezone().isoformat(timespec="seconds")


def canonical_bytes(value: Any) -> bytes:
    return (
        json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":"))
        + "\n"
    ).encode("utf-8")


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_json(value: Any) -> str:
    return sha256_bytes(canonical_bytes(value))


def load_records(path: Path) -> list[dict[str, Any]]:
    text = path.read_text(encoding="utf-8")
    if path.suffix.lower() == ".jsonl":
        rows = []
        for line_no, line in enumerate(text.splitlines(), start=1):
            if not line.strip():
                continue
            row = json.loads(line)
            if not isinstance(row, dict):
                raise ValueError(f"{path}:{line_no}: expected JSON object")
            rows.append(row)
        return rows

    payload = json.loads(text)
    if isinstance(payload, list):
        rows = payload
    elif isinstance(payload, dict):
        rows = None
        for key in ("records", "items", "docs", "results"):
            candidate = payload.get(key)
            if isinstance(candidate, list):
                rows = candidate
                break
        if rows is None:
            raise ValueError(
                "input JSON object must contain one of records/items/docs/results"
            )
    else:
        raise ValueError("input JSON must be an array or object containing an array")

    out: list[dict[str, Any]] = []
    for i, row in enumerate(rows):
        if not isinstance(row, dict):
            raise ValueError(f"record {i} is not an object")
        out.append(row)
    return out


def first_text(row: dict[str, Any], *keys: str) -> str:
    for key in keys:
        value = row.get(key)
        if isinstance(value, str) and value.strip():
            return value.strip()
    return ""


def normalize_id(value: str) -> str:
    return " ".join(value.split()).strip()


def source_identity(row: dict[str, Any]) -> str:
    eric_id = first_text(row, "ID", "id", "ERICNumber", "eric_id", "ericId")
    if eric_id:
        return f"ERIC:{normalize_id(eric_id)}"

    doi = first_text(row, "DOI", "doi")
    if doi:
        return f"DOI:{normalize_id(doi).lower()}"

    title = first_text(row, "Title", "title")
    year = first_text(row, "PublicationDate", "publication_date", "Year", "year")
    author = first_text(row, "Author", "Authors", "author", "authors")
    fallback = {
        "title": title,
        "year": year,
        "author": author,
        "metadata_sha256": sha256_json(row),
    }
    return "METADATA:" + sha256_json(fallback)


def title_abstract_snapshot(row: dict[str, Any]) -> dict[str, Any]:
    return {
        "title": first_text(row, "Title", "title"),
        "abstract": first_text(
            row,
            "Description",
            "description",
            "Abstract",
            "abstract",
            "Summary",
            "summary",
        ),
        "subject": row.get("Subject", row.get("subject", row.get("subjects"))),
        "publication_type": row.get(
            "PublicationType",
            row.get(
                "publication_type",
                row.get("publication_types", row.get("DocumentType")),
            ),
        ),
        "peer_reviewed": row.get("PeerReviewed", row.get("peer_reviewed")),
    }


def load_overrides(path: Path | None) -> dict[str, dict[str, Any]]:
    if path is None:
        return {}
    out: dict[str, dict[str, Any]] = {}
    with path.open("r", encoding="utf-8") as handle:
        for line_no, line in enumerate(handle, start=1):
            if not line.strip():
                continue
            row = json.loads(line)
            if not isinstance(row, dict):
                raise ValueError(f"override line {line_no} is not an object")
            source_ref = str(row.get("source_identity_reference") or "").strip()
            decision = str(row.get("decision") or "").strip()
            if not source_ref:
                raise ValueError(f"override line {line_no} lacks source identity")
            if decision not in ALLOWED_DECISIONS:
                raise ValueError(
                    f"override line {line_no} invalid decision {decision!r}"
                )
            reasons = row.get("reason_codes", [])
            if not isinstance(reasons, list) or not all(
                isinstance(x, str) for x in reasons
            ):
                raise ValueError(f"override line {line_no} reason_codes must be strings")
            unknown = sorted(set(reasons) - ALLOWED_REASON_CODES)
            if unknown:
                raise ValueError(
                    f"override line {line_no} unknown reason codes: {unknown}"
                )
            if source_ref in out:
                raise ValueError(
                    f"multiple overrides for {source_ref}; append-only supersession "
                    "must be represented explicitly in a later ledger generation"
                )
            out[source_ref] = row
    return out


def build_receipt(
    row: dict[str, Any],
    override: dict[str, Any] | None,
    *,
    rubric_version: str,
    rubric_reference: str,
    default_process_reference: str,
    input_sha256: str,
    generated_at: str,
) -> dict[str, Any]:
    source_ref = source_identity(row)
    metadata_sha = sha256_json(row)
    snapshot = title_abstract_snapshot(row)
    snapshot_sha = sha256_json(snapshot)

    if override is None:
        decision = "unresolved"
        reasons = ["awaitingScreeningReview"]
        free_text_reason = "screening decision not yet supplied"
        reviewer = "unassigned"
        process_ref = default_process_reference
        timestamp = generated_at
        supersedes = None
    else:
        decision = override["decision"]
        reasons = list(override.get("reason_codes", []))
        free_text_reason = str(override.get("free_text_reason") or "")
        reviewer = str(
            override.get("reviewer_or_model_reference") or "unspecified-reviewer"
        )
        process_ref = str(
            override.get("process_reference") or default_process_reference
        )
        timestamp = str(override.get("decision_timestamp") or generated_at)
        supersedes = override.get("supersedes_decision_reference")

    decision_identity_payload = {
        "source_identity_reference": source_ref,
        "metadata_sha256": metadata_sha,
        "title_abstract_snapshot_sha256": snapshot_sha,
        "rubric_version": rubric_version,
        "decision": decision,
        "reason_codes": reasons,
        "reviewer_or_model_reference": reviewer,
        "process_reference": process_ref,
        "decision_timestamp": timestamp,
        "supersedes_decision_reference": supersedes,
    }
    decision_ref = "screening-decision:" + sha256_json(decision_identity_payload)

    return {
        "schema": "digital-esd-title-abstract-screening-receipt-v1",
        "decision_reference": decision_ref,
        "source_identity_reference": source_ref,
        "input_set_sha256": input_sha256,
        "metadata_revision_reference": f"metadata-sha256:{metadata_sha}",
        "metadata_sha256": metadata_sha,
        "title_abstract_snapshot_reference": f"title-abstract-sha256:{snapshot_sha}",
        "title_abstract_snapshot_sha256": snapshot_sha,
        "title_abstract_snapshot": snapshot,
        "screening_rubric_reference": rubric_reference,
        "screening_rubric_version": rubric_version,
        "decision": decision,
        "reason_codes": reasons,
        "free_text_reason": free_text_reason,
        "reviewer_or_model_reference": reviewer,
        "process_reference": process_ref,
        "decision_timestamp": timestamp,
        "supersedes_decision_reference": supersedes,
        "exact_metadata_snapshot_retained": True,
        "exclusion_or_ambiguity_retained": True,
        "decision_creates_source_truth": False,
        "decision_creates_source_audit_admission": False,
        "decision_raises_claim_ceiling": False,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", required=True, type=Path)
    parser.add_argument("--decisions", type=Path)
    parser.add_argument(
        "--out-dir",
        default=Path("artifacts/digital-esd/screening"),
        type=Path,
    )
    parser.add_argument(
        "--rubric-version",
        default="digital-esd-title-abstract-screening-v1",
    )
    parser.add_argument(
        "--rubric-reference",
        default=(
            "docs/digital-esd-integrative-review-draft.md"
            "#4.6-exclusion-and-non-promotion-rules"
        ),
    )
    parser.add_argument(
        "--process-reference",
        default="scripts/prepare_digital_esd_screening_ledger.py",
    )
    args = parser.parse_args()

    raw_input = args.input.read_bytes()
    input_sha = sha256_bytes(raw_input)
    records = load_records(args.input)
    overrides = load_overrides(args.decisions)
    generated_at = now_iso()

    args.out_dir.mkdir(parents=True, exist_ok=True)
    ledger_path = args.out_dir / "screening-decisions.jsonl"

    counts = {key: 0 for key in ALLOWED_DECISIONS}
    seen: set[str] = set()
    applied_overrides: set[str] = set()

    with ledger_path.open("w", encoding="utf-8") as handle:
        for row in records:
            source_ref = source_identity(row)
            if source_ref in seen:
                raise RuntimeError(
                    f"deduplicated input contains duplicate stable source identity: {source_ref}"
                )
            seen.add(source_ref)
            override = overrides.get(source_ref)
            if override is not None:
                applied_overrides.add(source_ref)
            receipt = build_receipt(
                row,
                override,
                rubric_version=args.rubric_version,
                rubric_reference=args.rubric_reference,
                default_process_reference=args.process_reference,
                input_sha256=input_sha,
                generated_at=generated_at,
            )
            counts[receipt["decision"]] += 1
            handle.write(
                json.dumps(receipt, ensure_ascii=False, sort_keys=True) + "\n"
            )

    unapplied = sorted(set(overrides) - applied_overrides)
    if unapplied:
        raise RuntimeError(
            "decision overrides reference records absent from the exact input set: "
            + ", ".join(unapplied[:20])
        )

    ledger_sha = sha256_bytes(ledger_path.read_bytes())
    manifest = {
        "schema": "digital-esd-title-abstract-screening-ledger-v1",
        "input_deduplicated_set_reference": str(args.input),
        "input_deduplicated_set_sha256": input_sha,
        "input_record_count": len(records),
        "screening_rubric_reference": args.rubric_reference,
        "screening_rubric_version": args.rubric_version,
        "decision_overlay_reference": str(args.decisions) if args.decisions else None,
        "decision_ledger_reference": str(ledger_path),
        "decision_ledger_sha256": ledger_sha,
        "include_count": counts["include"],
        "probable_count": counts["probable"],
        "exclude_count": counts["exclude"],
        "unresolved_count": counts["unresolved"],
        "every_input_record_retained_in_ledger": True,
        "exclusions_retained": True,
        "ambiguities_retained": True,
        "supersession_append_only": True,
        "screening_creates_evidence_truth": False,
        "screening_creates_source_audit_admission": False,
        "generated_at": generated_at,
    }
    manifest_path = args.out_dir / "screening-manifest.json"
    manifest_path.write_text(
        json.dumps(manifest, indent=2, ensure_ascii=False, sort_keys=True) + "\n",
        encoding="utf-8",
    )

    print(
        "DIGITAL_ESD_SCREENING_LEDGER "
        f"records={len(records)} include={counts['include']} "
        f"probable={counts['probable']} exclude={counts['exclude']} "
        f"unresolved={counts['unresolved']} "
        f"ledger_sha256={ledger_sha}"
    )
    print(f"manifest: {manifest_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
