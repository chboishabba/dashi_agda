#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import sys
from copy import deepcopy
from pathlib import Path
from typing import Any

SCHEMA = "slr-claim-fragment-residual-inheritance-v1"
TARGET_SCHEMA = "sl.candidate_world_model.v0_1"
MAP_SCHEMA = "abc730-canonical-claim-residual-map-v1"


def load(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise SystemExit(f"expected JSON object: {path}")
    return value


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser()
    p.add_argument("--world", type=Path, required=True)
    p.add_argument("--residual-map", type=Path, required=True)
    p.add_argument("--output", type=Path, required=True)
    return p.parse_args()


def main() -> int:
    args = parse_args()
    world = load(args.world)
    residual_map = load(args.residual_map)

    if world.get("schema_version") != TARGET_SCHEMA:
        raise SystemExit("unexpected CandidateWorldModel schema")
    if residual_map.get("schema") != MAP_SCHEMA:
        raise SystemExit("unexpected canonical claim residual map schema")
    if bool((world.get("metadata") or {}).get("semantic_promotion", False)):
        raise SystemExit("refusing semantically promoted world model")
    if bool(residual_map.get("semantic_promotion", False)):
        raise SystemExit("residual map must not claim semantic promotion")

    out = deepcopy(world)
    claims = list(out.get("claims") or [])
    residuals = list(out.get("residuals") or [])
    map_claims = residual_map.get("claims") or {}
    if not isinstance(map_claims, dict):
        raise SystemExit("residual map claims must be an object")

    existing_residual_ids = {
        str(r.get("residual_id", "")) for r in residuals if isinstance(r, dict)
    }

    fragment_nodes = 0
    inherited_fragments = 0
    intermediate_fragments = 0
    inherited_obligations = 0
    unmapped_claim_fragments = 0

    for node in claims:
        if not isinstance(node, dict):
            continue
        kind = str(node.get("node_kind", ""))
        metadata = node.get("metadata") or {}
        if kind not in {"canonical_claim_local_fragment", "intermediate_discourse_fragment"}:
            continue
        fragment_nodes += 1
        if kind == "intermediate_discourse_fragment":
            intermediate_fragments += 1
            metadata = dict(metadata)
            metadata["canonical_claim_residual_inheritance"] = {
                "schema": SCHEMA,
                "inheritance_state": "not-applicable-intermediate-fragment",
                "canonical_claim_ref": "",
                "inherited_obligation_ids": [],
                "adjacency_does_not_assign_claim": True,
                "semantic_promotion": False,
            }
            node["metadata"] = metadata
            continue

        claim_ref = str(metadata.get("claim_ref", ""))
        spec = map_claims.get(claim_ref)
        if not isinstance(spec, dict):
            unmapped_claim_fragments += 1
            metadata = dict(metadata)
            metadata["canonical_claim_residual_inheritance"] = {
                "schema": SCHEMA,
                "inheritance_state": "no-explicit-residual-map-entry",
                "canonical_claim_ref": claim_ref,
                "inherited_obligation_ids": [],
                "semantic_promotion": False,
            }
            node["metadata"] = metadata
            continue

        obligations = [o for o in (spec.get("obligations") or []) if isinstance(o, dict)]
        inherited_ids: list[str] = []
        for obligation in obligations:
            obligation_id = str(obligation.get("obligation_id", ""))
            if not obligation_id:
                continue
            residual_id = f"fragment-obligation:{node.get('node_id','')}:{obligation_id}"
            inherited_ids.append(obligation_id)
            if residual_id in existing_residual_ids:
                continue
            residuals.append({
                "residual_id": residual_id,
                "candidate_id": node.get("node_id", ""),
                "status": "candidate",
                "residual_kind": "canonical_claim_consumer_obligation",
                "canonical_claim_ref": claim_ref,
                "obligation_id": obligation_id,
                "obligation_status": obligation.get("status", "open"),
                "owner_reference": obligation.get("owner_reference", ""),
                "payment_reference": obligation.get("payment_reference", ""),
                "evidence_kind_required": obligation.get("evidence_kind_required", ""),
                "inheritance_scope": "claim-local fragment inherits consumer/evidence debt only",
                "whole_claim_extent_paid": False,
                "claim_truth_promoted": False,
                "semantic_promotion": False,
                "source_anchor_ids": list(node.get("source_anchor_ids") or []),
            })
            existing_residual_ids.add(residual_id)
            inherited_obligations += 1

        node_residual = dict(node.get("residual") or {})
        node_residual["canonical_claim_consumer_obligations"] = inherited_ids
        node_residual["canonical_claim_current_first_residual"] = spec.get("current_first_residual", "")
        node_residual["whole_claim_extent_paid"] = False
        node_residual["claim_truth_promoted"] = False
        node["residual"] = node_residual

        metadata = dict(metadata)
        metadata["canonical_claim_residual_inheritance"] = {
            "schema": SCHEMA,
            "inheritance_state": "explicit-map-entry-applied",
            "canonical_claim_ref": claim_ref,
            "consumer_reference": spec.get("consumer_reference", ""),
            "claim_role": spec.get("claim_role", ""),
            "inherited_obligation_ids": inherited_ids,
            "whole_claim_extent_paid": False,
            "claim_truth_promoted": False,
            "semantic_promotion": False,
        }
        node["metadata"] = metadata
        inherited_fragments += 1

    out["claims"] = claims
    out["residuals"] = residuals
    metadata = dict(out.get("metadata") or {})
    metadata["claim_fragment_residual_inheritance"] = {
        "schema": SCHEMA,
        "residual_map_schema": MAP_SCHEMA,
        "residual_map_reference": str(args.residual_map),
        "claim_local_fragments_inherit_consumer_debt": True,
        "intermediate_fragments_inherit_adjacent_claim_debt": False,
        "whole_claim_extent_paid_by_inheritance": False,
        "claim_truth_promoted_by_inheritance": False,
        "append_only": True,
        "candidate_only": True,
        "semantic_promotion": False,
    }
    out["metadata"] = metadata

    summary = dict(out.get("summary") or {})
    summary.update({
        "claim_fragment_residual_inheritance_fragment_count": fragment_nodes,
        "claim_fragment_residual_inheritance_mapped_fragment_count": inherited_fragments,
        "claim_fragment_residual_inheritance_intermediate_fragment_count": intermediate_fragments,
        "claim_fragment_residual_inheritance_obligation_count": inherited_obligations,
        "claim_fragment_residual_inheritance_unmapped_claim_fragment_count": unmapped_claim_fragments,
    })
    out["summary"] = summary

    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(out, indent=2, ensure_ascii=False, sort_keys=True) + "\n", encoding="utf-8")
    print(
        "SLR_CLAIM_FRAGMENT_RESIDUAL_INHERITANCE_RECEIPT "
        f"schema={SCHEMA} fragments={fragment_nodes} mapped_fragments={inherited_fragments} "
        f"intermediate_fragments={intermediate_fragments} obligations={inherited_obligations} "
        f"unmapped_claim_fragments={unmapped_claim_fragments} "
        "intermediate_inherits_adjacent_claim=false whole_claim_extent_paid=false "
        "claim_truth_promoted=false append_only=true candidate_only=true semantic_promotion=false",
        file=sys.stderr,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
