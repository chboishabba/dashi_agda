#!/usr/bin/env python3
"""Prepare the Digital-ESD P0-G full-text escalation and canonical evidence handoff.

Only authoritative screening receipts with decision include/probable may enter
this worklist.

Without --retrieved, the tool emits the retrieval worklist only.

With --retrieved, each retrieved row must contain:
  source_identity_reference
  artifact_path
  sha256
  retrieval_reference
  retrieval_timestamp
  manifestation_family

The tool emits canonical evidence-preparation coordinates and an optional
compatibility JSONL for the historical Python SLR source-unit batch.  Neither
output creates SourceAuditAdmission or source truth.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any


RETAINED = {"include", "probable"}
FAMILIES = {
    "pdf_document": "PdfDocument",
    "legal_authority": "LegalAuthority",
    "other_evidence": "Other",
    "scholarly_full_text": "Other",
}


def canonical_bytes(value: Any) -> bytes:
    return (json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":")) + "\n").encode("utf-8")


def sha256_json(value: Any) -> str:
    return hashlib.sha256(canonical_bytes(value)).hexdigest()


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as fh:
        while True:
            chunk = fh.read(1024 * 1024)
            if not chunk:
                break
            h.update(chunk)
    return h.hexdigest()


def read_jsonl(path: Path) -> list[dict[str, Any]]:
    rows = []
    with path.open("r", encoding="utf-8") as fh:
        for n, line in enumerate(fh, 1):
            if not line.strip():
                continue
            row = json.loads(line)
            if not isinstance(row, dict):
                raise ValueError(f"{path}:{n}: expected object")
            rows.append(row)
    return rows


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--ledger", required=True, type=Path)
    ap.add_argument("--retrieved", type=Path)
    ap.add_argument("--out-dir", type=Path, default=Path("artifacts/digital-esd/fulltext"))
    ap.add_argument("--verify-files", action="store_true")
    args = ap.parse_args()

    ledger_rows = read_jsonl(args.ledger)
    ledger_by_ref = {str(r["source_identity_reference"]): r for r in ledger_rows}

    retained_rows = [
        r for r in ledger_rows
        if str(r.get("decision") or "") in RETAINED
    ]

    args.out_dir.mkdir(parents=True, exist_ok=True)
    worklist_path = args.out_dir / "fulltext-worklist.jsonl"

    with worklist_path.open("w", encoding="utf-8") as fh:
        for row in retained_rows:
            payload = {
                "source_identity_reference": row["source_identity_reference"],
                "decision_reference": row["decision_reference"],
                "decision": row["decision"],
                "metadata_sha256": row["metadata_sha256"],
            }
            receipt = {
                "schema": "digital-esd-fulltext-escalation-v1",
                **payload,
                "fulltext_request_reference": "fulltext-request:" + sha256_json(payload),
                "fulltext_retrieval_process_reference": "external-fulltext-retrieval",
                "retrieval_status_reference": "not-yet-observed",
                "retrieval_creates_source_truth": False,
                "retrieval_creates_source_audit_admission": False,
            }
            fh.write(json.dumps(receipt, ensure_ascii=False, sort_keys=True) + "\n")

    retrieved_rows = read_jsonl(args.retrieved) if args.retrieved else []
    retrieved_by_ref = {
        str(r["source_identity_reference"]): r for r in retrieved_rows
    }
    extra = sorted(set(retrieved_by_ref) - {str(r["source_identity_reference"]) for r in retained_rows})
    if extra:
        raise RuntimeError(
            "retrieved artifacts supplied for sources without authoritative "
            f"include/probable decisions: {extra[:20]}"
        )

    canonical_path = args.out_dir / "canonical-fulltext-evidence.jsonl"
    adapter_path = args.out_dir / "slr-source-unit-adapter.jsonl"

    canonical_rows = []
    adapter_rows = []

    for ref, retrieved in sorted(retrieved_by_ref.items()):
        ledger = ledger_by_ref[ref]
        digest = str(retrieved.get("sha256") or "").lower().removeprefix("sha256:")
        if len(digest) != 64:
            raise ValueError(f"{ref}: retrieved sha256 must be a 64-hex digest")
        int(digest, 16)

        artifact_text = str(retrieved.get("artifact_path") or "").strip()
        if not artifact_text:
            raise ValueError(f"{ref}: retrieved artifact_path is required")
        artifact_path = Path(artifact_text)
        if args.verify_files:
            if not artifact_path.exists():
                raise FileNotFoundError(f"{ref}: {artifact_path}")
            observed = sha256_file(artifact_path)
            if observed != digest:
                raise RuntimeError(
                    f"{ref}: artifact digest mismatch expected={digest} observed={observed}"
                )

        family_key = str(retrieved.get("manifestation_family") or "scholarly_full_text")
        if family_key not in FAMILIES:
            raise ValueError(f"{ref}: unsupported manifestation_family {family_key!r}")

        revision_ref = f"fulltext-sha256:{digest}"
        manifestation_ref = f"manifestation:{revision_ref}"
        evidence_payload = {
            "source_identity_reference": ref,
            "screening_decision_reference": ledger["decision_reference"],
            "screening_decision": ledger["decision"],
            "artifact_path": str(artifact_path),
            "artifact_sha256": digest,
            "manifestation_ref": manifestation_ref,
            "manifestation_family": FAMILIES[family_key],
            "source_revision_ref": revision_ref,
            "content_digest_ref": f"sha256:{digest}",
            "acquisition_receipt_ref": retrieved["retrieval_reference"],
            "retrieval_timestamp": retrieved["retrieval_timestamp"],
        }
        canonical_rows.append({
            "schema": "digital-esd-canonical-fulltext-evidence-preparation-v1",
            **evidence_payload,
            "span_kind": "WholeRevision",
            "candidate_only": True,
            "creates_semantic_authority": False,
            "applicability_promoted": False,
            "claim_truth_promoted": False,
            "creates_source_audit_admission": False,
        })

        # The historical Python SLR batch consumes text, not arbitrary PDFs.
        # Emit an adapter row only when an explicit materialised text path is
        # supplied.  Canonical manifestation/revision preparation does not
        # depend on this compatibility adapter.
        text_path = str(retrieved.get("text_path") or "").strip()
        if text_path:
            adapter_rows.append({
                "source_unit_ref": f"digital-esd:{ref}:{digest}",
                "source_kind": "scholarly-full-text",
                "source_role": "screened-digital-esd-study",
                "language": str(retrieved.get("language") or "en"),
                "revision_ref": revision_ref,
                "text_path": text_path,
                "canonical_evidence_manifestation_ref": manifestation_ref,
                "adapter_is_production_semantic_abi": False,
            })

    with canonical_path.open("w", encoding="utf-8") as fh:
        for row in canonical_rows:
            fh.write(json.dumps(row, ensure_ascii=False, sort_keys=True) + "\n")
    with adapter_path.open("w", encoding="utf-8") as fh:
        for row in adapter_rows:
            fh.write(json.dumps(row, ensure_ascii=False, sort_keys=True) + "\n")

    manifest = {
        "schema": "digital-esd-fulltext-handoff-manifest-v1",
        "screening_ledger_reference": str(args.ledger),
        "input_screening_record_count": len(ledger_rows),
        "authoritative_retained_or_probable_count": len(retained_rows),
        "retrieved_artifact_count": len(retrieved_rows),
        "canonical_evidence_preparation_count": len(canonical_rows),
        "fulltext_retrieval_creates_source_truth": False,
        "fulltext_retrieval_creates_source_audit_admission": False,
        "slr_adapter_is_production_semantic_abi": False,
        "source_audit_admission_remains_separate": True,
    }
    (args.out_dir / "fulltext-handoff-manifest.json").write_text(
        json.dumps(manifest, indent=2, ensure_ascii=False, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    print(json.dumps(manifest, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
