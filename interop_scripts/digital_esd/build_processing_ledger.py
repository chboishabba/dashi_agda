#!/usr/bin/env python3
"""Build the exact per-study Digital-ESD processing ledger.

This is a thin application-side join over already-authoritative artifacts.
It does not create screening decisions, reviewed evidence, or admission.

Every metadata row remains in the output denominator. Later stages require
explicit same-source receipts; they are never inferred merely because a still
later receipt exists.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
from pathlib import Path
from typing import Any


EXPECTED_METADATA = 43996
RETAINED = {"include", "probable"}


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as fh:
        for chunk in iter(lambda: fh.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def read_tsv(path: Path) -> list[dict[str, str]]:
    with path.open(newline="", encoding="utf-8") as fh:
        return [dict(row) for row in csv.DictReader(fh, delimiter="\t")]


def read_jsonl(path: Path | None) -> list[dict[str, Any]]:
    if path is None or not path.exists():
        return []
    out: list[dict[str, Any]] = []
    with path.open("r", encoding="utf-8") as fh:
        for n, line in enumerate(fh, 1):
            if not line.strip():
                continue
            row = json.loads(line)
            if not isinstance(row, dict):
                raise ValueError(f"{path}:{n}: expected object")
            out.append(row)
    return out


def identity(row: dict[str, Any]) -> str:
    for key in (
        "source_identity_reference",
        "sourceIdentityReference",
        "source_ref",
    ):
        value = row.get(key)
        if isinstance(value, str) and value.strip():
            return value.strip()
    return ""


def explicit_screened(row: dict[str, str]) -> bool:
    decision = str(row.get("decision") or "").strip()
    reviewer = str(
        row.get("reviewer_or_model_reference")
        or row.get("reviewer_or_process_reference")
        or row.get("reviewed_by")
        or ""
    ).strip()
    reviewed_flag = str(row.get("reviewed") or "").strip().lower()
    return (
        decision in {"include", "probable", "exclude"}
        or reviewer not in {"", "unassigned"}
        or reviewed_flag in {"true", "1", "yes"}
    )


def map_unique(rows: list[dict[str, Any]], label: str) -> dict[str, dict[str, Any]]:
    out: dict[str, dict[str, Any]] = {}
    for row in rows:
        ref = identity(row)
        if not ref:
            raise ValueError(f"{label}: row lacks stable source identity")
        if ref in out:
            raise ValueError(f"{label}: duplicate receipt for {ref}")
        out[ref] = row
    return out


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--screening-ledger", type=Path, required=True)
    ap.add_argument("--fulltext-index", type=Path, required=True)
    ap.add_argument("--materialization-receipts", type=Path)
    ap.add_argument("--slr-handoff", type=Path)
    ap.add_argument("--slr-parse-receipts", type=Path)
    ap.add_argument("--slr-review-receipts", type=Path)
    ap.add_argument("--source-audit-receipts", type=Path)
    ap.add_argument("--output-ledger", type=Path, required=True)
    ap.add_argument("--output-manifest", type=Path, required=True)
    ap.add_argument("--expected-metadata-count", type=int, default=EXPECTED_METADATA)
    args = ap.parse_args()

    screening = read_tsv(args.screening_ledger)
    if len(screening) != args.expected_metadata_count:
        raise RuntimeError(
            f"screening denominator mismatch: observed={len(screening)} "
            f"expected={args.expected_metadata_count}"
        )

    screen_by_ref: dict[str, dict[str, str]] = {}
    for row in screening:
        ref = identity(row)
        if not ref:
            raise ValueError("screening ledger row lacks source_identity_reference")
        if ref in screen_by_ref:
            raise ValueError(f"screening ledger duplicate identity: {ref}")
        screen_by_ref[ref] = row

    fulltext_rows = read_tsv(args.fulltext_index)
    fulltext_by_ref = map_unique(fulltext_rows, "fulltext-index")
    materialized = map_unique(read_jsonl(args.materialization_receipts), "materialization")
    handoff = map_unique(read_jsonl(args.slr_handoff), "slr-handoff")
    parsed = map_unique(read_jsonl(args.slr_parse_receipts), "slr-parse")
    reviewed = map_unique(read_jsonl(args.slr_review_receipts), "slr-review")
    admitted = map_unique(read_jsonl(args.source_audit_receipts), "source-audit")

    denominator = set(screen_by_ref)
    for label, mapping in (
        ("fulltext-index", fulltext_by_ref),
        ("materialization", materialized),
        ("slr-handoff", handoff),
        ("slr-parse", parsed),
        ("slr-review", reviewed),
        ("source-audit", admitted),
    ):
        orphan = sorted(set(mapping) - denominator)
        if orphan:
            raise RuntimeError(f"{label}: orphan identities outside denominator: {orphan[:20]}")

    rows_out: list[dict[str, Any]] = []
    counts = {
        "metadata_records": len(screening),
        "genuinely_screened_records": 0,
        "include_probable_eligible": 0,
        "verified_fulltext_artifacts": 0,
        "materialised_texts": 0,
        "handed_to_slr": 0,
        "successfully_parsed_by_slr": 0,
        "reviewed_canonical_evidence": 0,
        "source_audit_admission_complete": 0,
    }

    for ref in sorted(denominator):
        screen = screen_by_ref[ref]
        decision = str(screen.get("decision") or "unresolved").strip()
        screened = explicit_screened(screen)
        retained = screened and decision in RETAINED

        ft = fulltext_by_ref.get(ref)
        verified = bool(ft and str(ft.get("status") or "") == "verified")
        materialised = ref in materialized
        handed = ref in handoff
        parse = ref in parsed
        review = ref in reviewed
        admission = ref in admitted

        checks = {
            "retained_implies_screened": (not retained) or screened,
            "fulltext_implies_retained": (not verified) or retained,
            "materialisation_implies_fulltext": (not materialised) or verified,
            "handoff_implies_materialisation": (not handed) or materialised,
            "parse_implies_handoff": (not parse) or handed,
            "review_implies_parse": (not review) or parse,
            "admission_implies_review": (not admission) or review,
        }
        failed = [name for name, ok in checks.items() if not ok]
        if failed:
            raise RuntimeError(
                f"{ref}: stage-containment failure(s): {', '.join(failed)}"
            )

        counts["genuinely_screened_records"] += int(screened)
        counts["include_probable_eligible"] += int(retained)
        counts["verified_fulltext_artifacts"] += int(verified)
        counts["materialised_texts"] += int(materialised)
        counts["handed_to_slr"] += int(handed)
        counts["successfully_parsed_by_slr"] += int(parse)
        counts["reviewed_canonical_evidence"] += int(review)
        counts["source_audit_admission_complete"] += int(admission)

        metadata_revision = str(
            screen.get("metadata_revision_reference")
            or screen.get("metadataRevisionReference")
            or ""
        )
        row_basis = {
            "source_identity_reference": ref,
            "metadata_revision_reference": metadata_revision,
            "screened": screened,
            "retained": retained,
            "verified": verified,
            "materialised": materialised,
            "handoff": handed,
            "parsed": parse,
            "reviewed": review,
            "admitted": admission,
        }
        receipt_ref = "study-processing-row:" + hashlib.sha256(
            json.dumps(row_basis, sort_keys=True, separators=(",", ":")).encode("utf-8")
        ).hexdigest()

        rows_out.append({
            "schema": "digital-esd-study-processing-row-v1",
            "row_receipt_reference": receipt_ref,
            **row_basis,
            "screening_decision": decision,
            "fulltext_status": str(ft.get("status") if ft else "not-materialised"),
            "retained_implies_screened_observed": checks["retained_implies_screened"],
            "fulltext_implies_retained_observed": checks["fulltext_implies_retained"],
            "materialisation_implies_fulltext_observed": checks["materialisation_implies_fulltext"],
            "handoff_implies_materialisation_observed": checks["handoff_implies_materialisation"],
            "parse_implies_handoff_observed": checks["parse_implies_handoff"],
            "review_implies_parse_observed": checks["review_implies_parse"],
            "admission_implies_review_observed": checks["admission_implies_review"],
            "later_stage_inferred_without_receipt": False,
        })

    args.output_ledger.parent.mkdir(parents=True, exist_ok=True)
    with args.output_ledger.open("w", encoding="utf-8") as fh:
        for row in rows_out:
            fh.write(json.dumps(row, ensure_ascii=False, sort_keys=True) + "\n")

    manifest = {
        "schema": "digital-esd-study-processing-ledger-manifest-v1",
        "screening_ledger_reference": str(args.screening_ledger),
        "screening_ledger_sha256": sha256_file(args.screening_ledger),
        "fulltext_index_reference": str(args.fulltext_index),
        "fulltext_index_sha256": sha256_file(args.fulltext_index),
        "processing_ledger_reference": str(args.output_ledger),
        "processing_ledger_sha256": sha256_file(args.output_ledger),
        "processing_row_count": len(rows_out),
        "processing_row_count_matches_expected": len(rows_out) == args.expected_metadata_count,
        "every_metadata_record_has_processing_row": True,
        "stage_containment_checked_per_row": True,
        "later_stage_inference_forbidden_per_row": True,
        **counts,
    }
    args.output_manifest.parent.mkdir(parents=True, exist_ok=True)
    args.output_manifest.write_text(
        json.dumps(manifest, indent=2, ensure_ascii=False, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    print(json.dumps(manifest, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
