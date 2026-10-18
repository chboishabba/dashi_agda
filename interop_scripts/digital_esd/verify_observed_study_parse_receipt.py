#!/usr/bin/env python3
"""Verify one observed Digital-ESD retained-study parse receipt.

Expected directory:
  requests.jsonl
  verified.jsonl
  parser-output.jsonl

The verifier checks that all three artifacts describe the same source revision,
that the parser output matches the verified materialisation counts/hashes, and
that parser/facet outputs remain candidate-only and non-admitting.

It does not infer study truth or SourceAuditAdmission.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any


EXPECTED_FACETS = {
    "Population",
    "Sample",
    "Intervention",
    "Outcome",
    "StudyDesign",
    "Setting",
    "TimePeriod",
    "Method",
    "Limitation",
    "Funding",
    "Institution",
    "ParticipantGroup",
    "Measurement",
}


def read_one_jsonl(path: Path) -> dict[str, Any]:
    rows = []
    with path.open("r", encoding="utf-8") as handle:
        for n, line in enumerate(handle, 1):
            if not line.strip():
                continue
            value = json.loads(line)
            if not isinstance(value, dict):
                raise ValueError(f"{path}:{n}: expected JSON object")
            rows.append(value)
    if len(rows) != 1:
        raise ValueError(f"{path}: expected exactly one non-empty row, got {len(rows)}")
    return rows[0]


def canonical_bytes(value: Any) -> bytes:
    return (
        json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":"))
        + "\n"
    ).encode("utf-8")


def sha256_json(value: Any) -> str:
    return hashlib.sha256(canonical_bytes(value)).hexdigest()


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--receipt-dir", type=Path, required=True)
    ap.add_argument("--out", type=Path)
    args = ap.parse_args()

    root = args.receipt_dir
    request = read_one_jsonl(root / "requests.jsonl")
    verified = read_one_jsonl(root / "verified.jsonl")
    parsed = read_one_jsonl(root / "parser-output.jsonl")

    source_ref = request["source_identity_reference"]
    revision_ref = request["source_revision_reference"]
    source_sha = request["content_sha256"]

    for label, row in (("verified", verified), ("parsed", parsed)):
        require(
            row.get("source_identity_reference") == source_ref,
            f"{label}: source identity mismatch",
        )
        require(
            row.get("source_revision_reference") == revision_ref,
            f"{label}: source revision mismatch",
        )
        require(
            row.get("content_sha256") == source_sha,
            f"{label}: source content SHA-256 mismatch",
        )

    extraction = parsed.get("extraction_receipt") or {}
    require(
        verified["extracted_text_sha256"] == parsed["extracted_text_sha256"],
        "derived text digest mismatch",
    )
    require(
        verified["extracted_text_sha256"] == extraction.get("extracted_text_sha256"),
        "extraction receipt derived text digest mismatch",
    )
    require(
        verified["page_count"] == parsed["page_count"] == extraction.get("page_count"),
        "page count mismatch",
    )
    require(
        verified["document_node_count"] == len(parsed.get("document_nodes", [])),
        "document node count mismatch",
    )
    require(
        verified["study_facet_count"] == len(parsed.get("study_facets", [])),
        "study facet count mismatch",
    )

    observed_facets = {str(x.get("facet_role")) for x in parsed.get("study_facets", [])}
    require(
        observed_facets == EXPECTED_FACETS,
        f"facet role set mismatch: observed={sorted(observed_facets)}",
    )

    require(parsed.get("parser_success") is True, "parser_success != true")

    for label, row in (
        ("request", request),
        ("verified", verified),
        ("parsed", parsed),
        ("extraction", extraction),
    ):
        require(row.get("candidate_only") is True, f"{label}: candidate_only != true")
        require(
            row.get("creates_semantic_authority") is False,
            f"{label}: creates_semantic_authority != false",
        )
        require(
            row.get("applicability_promoted") is False,
            f"{label}: applicability_promoted != false",
        )
        require(
            row.get("claim_truth_promoted") is False,
            f"{label}: claim_truth_promoted != false",
        )

    require(
        parsed.get("creates_source_audit_admission") is False,
        "parser output creates_source_audit_admission != false",
    )
    require(
        parsed.get("creates_study_truth") is False,
        "parser output creates_study_truth != false",
    )
    for facet in parsed.get("study_facets", []):
        require(facet.get("candidate_only") is True, "facet candidate_only != true")
        require(
            facet.get("creates_source_audit_admission") is False,
            "facet creates_source_audit_admission != false",
        )
        require(
            facet.get("creates_study_truth") is False,
            "facet creates_study_truth != false",
        )

    manifest = {
        "schema": "digital-esd-observed-retained-study-parse-receipt-v1",
        "source_identity_reference": source_ref,
        "source_revision_reference": revision_ref,
        "source_artifact_sha256": source_sha,
        "source_artifact_path": request.get("artifact_path"),
        "extracted_text_sha256": verified["extracted_text_sha256"],
        "extraction_engine": verified["extraction_engine"],
        "extraction_engine_version": verified["extraction_engine_version"],
        "page_count": verified["page_count"],
        "document_node_count": verified["document_node_count"],
        "study_facet_count": verified["study_facet_count"],
        "facet_roles": sorted(observed_facets),
        "parser_success": True,
        "candidate_only": True,
        "creates_study_truth": False,
        "creates_source_audit_admission": False,
        "request_receipt_sha256": sha256_json(request),
        "verified_receipt_sha256": sha256_json(verified),
        "parser_output_sha256": sha256_json(parsed),
        "receipt_directory": str(root),
    }

    out = args.out or (root / "first-retained-study-parse-verification.json")
    out.write_text(
        json.dumps(manifest, ensure_ascii=False, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    print(json.dumps(manifest, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
