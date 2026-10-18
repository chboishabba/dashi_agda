#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

PACKET_SCHEMA = "sensiblaw.gwb-chronology-capstone-review-packet.v0_1"
TARGET_SCHEMA = "sensiblaw.gwb-heterogeneous-chronology-capstone.v0_1"
PROJECTION_SCHEMA = "sensiblaw.gwb-source-projection.v0_1"


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser()
    p.add_argument("--projection-manifest", type=Path, required=True)
    p.add_argument("--source-roles", type=Path, required=True)
    p.add_argument("--output", type=Path, required=True)
    p.add_argument("--matter-ref", default="matter:gwb:heterogeneous-chronology-capstone")
    p.add_argument("--max-selected-statements", type=int, default=80)
    return p.parse_args()


def load_json(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise SystemExit(f"expected JSON object: {path}")
    return value


def load_jsonl(path: Path) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for line_no, raw in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        if not raw.strip():
            continue
        value = json.loads(raw)
        if not isinstance(value, dict):
            raise SystemExit(f"expected JSON object at {path}:{line_no}")
        rows.append(value)
    return rows


def main() -> int:
    args = parse_args()
    if args.max_selected_statements <= 0:
        raise SystemExit("--max-selected-statements must be positive")

    projection = load_json(args.projection_manifest)
    if projection.get("schema_version") != PROJECTION_SCHEMA:
        raise SystemExit(
            f"unexpected projection schema: {projection.get('schema_version')!r}"
        )

    roles = load_jsonl(args.source_roles)
    role_by_ordinal: dict[int, dict[str, Any]] = {}
    for row in roles:
        ordinal = int(row["document_ordinal"])
        if ordinal in role_by_ordinal:
            raise SystemExit(f"duplicate source-role row for document {ordinal}")
        if bool(row.get("semantic_promotion", False)):
            raise SystemExit(f"source-role row {ordinal} claims semantic promotion")
        if not bool(row.get("candidate_only", False)):
            raise SystemExit(f"source-role row {ordinal} is not candidate-only")
        role_by_ordinal[ordinal] = row

    docs = projection.get("documents") or []
    if not isinstance(docs, list) or not docs:
        raise SystemExit("projection manifest has no documents")

    inventory: list[dict[str, Any]] = []
    seen: set[int] = set()
    for doc in docs:
        if not isinstance(doc, dict):
            raise SystemExit("projection document is not an object")
        ordinal = int(doc["document_ordinal"])
        if ordinal in seen:
            raise SystemExit(f"duplicate projection document {ordinal}")
        seen.add(ordinal)
        role = role_by_ordinal.get(ordinal)
        if role is None:
            raise SystemExit(f"missing source-role row for document {ordinal}")

        inventory.append(
            {
                "document_ordinal": ordinal,
                "source_kind": str(doc.get("source_kind", "")),
                "source_sha256": str(doc.get("source_sha256", "")),
                "projected_sha256": str(doc.get("projected_sha256", "")),
                "family_refs": [str(x) for x in (doc.get("family_refs") or [])],
                "source_role": str(role.get("source_role", "")),
                "claim_relative_primary_for": [
                    str(x) for x in (role.get("claim_relative_primary_for") or [])
                ],
                "not_authority_for": [
                    str(x) for x in (role.get("not_authority_for") or [])
                ],
                "selection_status": "awaiting-reviewed-local-exact-span-selection",
                "selected_statement_keys": [],
            }
        )

    if set(role_by_ordinal) != seen:
        extra = sorted(set(role_by_ordinal) - seen)
        raise SystemExit(f"source-role rows without projection documents: {extra}")

    packet = {
        "schema": PACKET_SCHEMA,
        "target_manifest_schema": TARGET_SCHEMA,
        "matter_ref": args.matter_ref,
        "projection_manifest": str(args.projection_manifest),
        "source_roles": str(args.source_roles),
        "max_selected_statements": args.max_selected_statements,
        "document_count": len(inventory),
        "documents": sorted(inventory, key=lambda row: row["document_ordinal"]),
        "review_requirements": {
            "local_retained_source_required": True,
            "exact_document_ref_required": True,
            "exact_source_revision_ref_required": True,
            "exact_span_ref_required": True,
            "exact_start_end_char_required": True,
            "literal_text_required": True,
            "parser_receipt_ref_required": True,
            "candidate_pnf_ref_required": True,
            "observation_ref_required": True,
            "statement_review_required": True,
            "event_join_review_required": True,
            "automatic_same_event_join_allowed": False,
            "same_qid_pays_event_identity": False,
            "same_person_date_pays_event_identity": False,
            "similar_text_pays_event_identity": False,
            "relative_time_may_be_coerced_to_exact": False,
            "source_revision_change_means_world_change": False,
        },
        "recommended_operator_flow": [
            "select semantically overlapping statements across source families",
            "copy exact literal spans from locally retained source material",
            "run each selected statement through the ordinary M12 PNF/review path",
            "review proposed same-event groups explicitly",
            "review temporal assertions independently of event identity",
            "review proposition-root and claim-leaf joins explicitly",
            "seed S29 review items from unresolved real discrepancies",
            "materialize the final target manifest through sensiblaw-pg-source-store",
        ],
        "candidate_only": True,
        "semantic_promotion": False,
    }

    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(
        json.dumps(packet, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    print(
        "GWB_CHRONOLOGY_REVIEW_PACKET "
        f"documents={len(inventory)} max_selected={args.max_selected_statements} "
        "exact_local_span_required=true automatic_event_join=false "
        "candidate_only=true semantic_promotion=false"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
