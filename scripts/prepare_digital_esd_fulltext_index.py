#!/usr/bin/env python3
"""Compile verified retained/probable Digital-ESD full-text index rows.

Consumes the authoritative title/abstract screening ledger plus a retrieval
inventory JSONL. It computes the artifact SHA-256 itself and emits only rows
whose source is explicitly include/probable and has a same-object identity
review reference.

Retrieval inventory row:
{
  "source_identity_reference": "ERIC:EJ...",
  "text_path": "/path/to/extracted-or-retained-fulltext.txt",
  "full_text_artifact_reference": "...",
  "same_object_identity_review_reference": "identity-review:...",
  "retrieval_reference": "...",
  "retrieval_timestamp": "...",
  "language": "en"
}

This script does not create SourceAuditAdmission and does not decide screening.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any

RETAINED = {"include", "probable"}


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def read_jsonl(path: Path) -> list[dict[str, Any]]:
    out = []
    with path.open("r", encoding="utf-8") as f:
        for n, line in enumerate(f, 1):
            if not line.strip():
                continue
            row = json.loads(line)
            if not isinstance(row, dict):
                raise ValueError(f"{path}:{n}: row is not an object")
            out.append(row)
    return out


def write_jsonl(path: Path, rows: list[dict[str, Any]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as f:
        for row in rows:
            f.write(json.dumps(row, ensure_ascii=False, sort_keys=True) + "\n")


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--ledger", required=True, type=Path)
    ap.add_argument("--retrieval-inventory", required=True, type=Path)
    ap.add_argument("--output", required=True, type=Path)
    args = ap.parse_args()

    ledger_rows = read_jsonl(args.ledger)
    decisions: dict[str, dict[str, Any]] = {}
    for row in ledger_rows:
        src = str(row.get("source_identity_reference") or "").strip()
        if not src or src in decisions:
            raise ValueError(f"invalid/duplicate ledger source identity: {src!r}")
        decisions[src] = row

    inventory = read_jsonl(args.retrieval_inventory)
    out = []
    seen: set[str] = set()
    for row in inventory:
        src = str(row.get("source_identity_reference") or "").strip()
        if not src:
            raise ValueError("retrieval inventory row lacks source identity")
        if src in seen:
            raise ValueError(f"duplicate retrieval inventory row: {src}")
        seen.add(src)

        decision = decisions.get(src)
        if decision is None:
            raise ValueError(f"{src}: absent from exact screening ledger")
        if decision.get("decision") not in RETAINED:
            raise ValueError(
                f"{src}: full-text handoff requires explicit include/probable; "
                f"found {decision.get('decision')!r}"
            )

        path_text = str(row.get("text_path") or "").strip()
        identity_review = str(
            row.get("same_object_identity_review_reference") or ""
        ).strip()
        if not path_text:
            raise ValueError(f"{src}: missing text_path")
        if not identity_review:
            raise ValueError(f"{src}: missing same-object identity review reference")

        path = Path(path_text)
        if not path.is_file():
            raise ValueError(f"{src}: full-text artifact does not exist: {path}")

        digest = sha256_file(path)
        out.append({
            "schema": "digital-esd-verified-fulltext-index-v1",
            "source_identity_reference": src,
            "screening_decision_reference": decision.get("decision_reference"),
            "screening_decision": decision.get("decision"),
            "text_path": str(path),
            "full_text_artifact_reference": str(
                row.get("full_text_artifact_reference") or path
            ),
            "full_text_sha256": digest,
            "full_text_obtained": True,
            "full_text_unavailable": False,
            "same_object_identity_review_reference": identity_review,
            "retrieval_reference": str(row.get("retrieval_reference") or ""),
            "retrieval_timestamp": str(row.get("retrieval_timestamp") or ""),
            "language": str(row.get("language") or "en"),
            "source_audit_admitted": False,
            "rejected_after_full_text": False,
            "screening_creates_source_truth": False,
            "screening_creates_source_audit_admission": False,
        })

    write_jsonl(args.output, out)
    print(f"DIGITAL_ESD_FULLTEXT_INDEX retained={len(out)} output={args.output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
