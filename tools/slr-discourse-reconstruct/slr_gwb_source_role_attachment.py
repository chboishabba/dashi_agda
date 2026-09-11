#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import sys
from copy import deepcopy
from pathlib import Path
from typing import Any

SCHEMA = "slr-gwb-source-role-attachment-v1"
TARGET_SCHEMA = "sl.candidate_world_model.v0_1"


def load(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise SystemExit(f"expected JSON object: {path}")
    return value


def read_jsonl(path: Path) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for raw in path.read_text(encoding="utf-8").splitlines():
        if not raw.strip():
            continue
        row = json.loads(raw)
        if not isinstance(row, dict):
            raise SystemExit(f"expected JSON object row in {path}")
        rows.append(row)
    return rows


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser()
    p.add_argument("--world-model", type=Path, required=True)
    p.add_argument("--roles", type=Path, required=True)
    p.add_argument("--output-model", type=Path, required=True)
    p.add_argument("--output-sidecar", type=Path, required=True)
    return p.parse_args()


def main() -> int:
    args = parse_args()
    world = load(args.world_model)
    roles = read_jsonl(args.roles)

    if world.get("schema_version") != TARGET_SCHEMA:
        raise SystemExit(f"unexpected CandidateWorldModel schema: {world.get('schema_version')!r}")
    if bool((world.get("metadata") or {}).get("semantic_promotion", False)):
        raise SystemExit("refusing semantically promoted input")

    by_ordinal: dict[int, dict[str, Any]] = {}
    for role in roles:
        ordinal = int(role.get("document_ordinal", -1))
        if ordinal < 0 or ordinal in by_ordinal:
            raise SystemExit(f"invalid/duplicate document_ordinal in role atlas: {ordinal}")
        if bool(role.get("semantic_promotion", False)):
            raise SystemExit("source-role atlas attempted semantic promotion")
        if not bool(role.get("candidate_only", False)):
            raise SystemExit("source-role atlas must remain candidate-only")
        by_ordinal[ordinal] = role

    provenance = [r for r in (world.get("provenance_graph") or []) if isinstance(r, dict)]
    provenance_ordinals = {int(r["document_ordinal"]) for r in provenance if "document_ordinal" in r}
    if set(by_ordinal) != provenance_ordinals:
        raise SystemExit(
            f"source-role/document mismatch roles={sorted(by_ordinal)} provenance={sorted(provenance_ordinals)}"
        )

    out = deepcopy(world)
    attached = 0
    primary_claim_classes = 0
    negative_authority_constraints = 0
    for record in out.get("provenance_graph") or []:
        if not isinstance(record, dict) or "document_ordinal" not in record:
            continue
        ordinal = int(record["document_ordinal"])
        role = by_ordinal[ordinal]
        primary_for = [str(x) for x in (role.get("claim_relative_primary_for") or [])]
        not_authority_for = [str(x) for x in (role.get("not_authority_for") or [])]
        record["claim_relative_source_role"] = {
            "schema": SCHEMA,
            "source_role": str(role.get("source_role", "")),
            "claim_relative_primary_for": primary_for,
            "not_authority_for": not_authority_for,
            "source_role_is_source_identity": False,
            "source_role_creates_claim_truth": False,
            "primaryness_is_claim_relative": True,
            "candidate_only": True,
            "semantic_promotion": False,
        }
        attached += 1
        primary_claim_classes += len(primary_for)
        negative_authority_constraints += len(not_authority_for)

    sidecar = {
        "schema": SCHEMA,
        "source_world_model_id": world.get("model_id", ""),
        "roles": [by_ordinal[o] for o in sorted(by_ordinal)],
        "summary": {
            "documents": len(by_ordinal),
            "roles_attached": attached,
            "primary_claim_classes": primary_claim_classes,
            "negative_authority_constraints": negative_authority_constraints,
        },
        "source_role_is_source_identity": False,
        "source_role_creates_claim_truth": False,
        "primaryness_is_claim_relative": True,
        "candidate_only": True,
        "semantic_promotion": False,
    }

    out.setdefault("projections", []).append({
        "projection_id": SCHEMA,
        "projection_kind": "gwb_claim_relative_source_role_attachment",
        "status": "candidate",
        "sidecar": str(args.output_sidecar),
        "roles_attached": attached,
        "primaryness_is_claim_relative": True,
        "source_role_creates_claim_truth": False,
        "semantic_promotion": False,
    })
    metadata = out.setdefault("metadata", {})
    metadata["gwb_claim_relative_source_roles"] = {
        "schema": SCHEMA,
        "sidecar": str(args.output_sidecar),
        **sidecar["summary"],
        "source_role_is_source_identity": False,
        "source_role_creates_claim_truth": False,
        "primaryness_is_claim_relative": True,
        "candidate_only": True,
        "semantic_promotion": False,
    }
    metadata["candidate_only"] = True
    metadata["semantic_promotion"] = False

    args.output_model.parent.mkdir(parents=True, exist_ok=True)
    args.output_sidecar.parent.mkdir(parents=True, exist_ok=True)
    args.output_model.write_text(json.dumps(out, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    args.output_sidecar.write_text(json.dumps(sidecar, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    print(
        "SLR_GWB_SOURCE_ROLE_ATTACHMENT_RECEIPT "
        f"schema={SCHEMA} documents={len(by_ordinal)} roles_attached={attached} "
        f"primary_claim_classes={primary_claim_classes} "
        f"negative_authority_constraints={negative_authority_constraints} "
        "primaryness_is_claim_relative=true source_role_is_source_identity=false "
        "source_role_creates_claim_truth=false candidate_only=true semantic_promotion=false",
        file=sys.stderr,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
