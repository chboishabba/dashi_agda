#!/usr/bin/env python3
from __future__ import annotations

import argparse
import copy
import json
import sys
from pathlib import Path
from typing import Any

SCHEMA = "slr-fragment-evidence-contraction-v1"
TARGET_SCHEMA = "sl.candidate_world_model.v0_1"


def load(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise SystemExit(f"expected JSON object: {path}")
    return value


def stable_source_id(manifest: dict[str, Any]) -> str:
    return str((manifest.get("ibrahim") or {}).get("stable_source_id", ""))


def claim_nodes(model: dict[str, Any]) -> dict[str, dict[str, Any]]:
    out: dict[str, dict[str, Any]] = {}
    for node in model.get("claims", []):
        if not isinstance(node, dict):
            continue
        ref = str((node.get("metadata") or {}).get("claim_ref", ""))
        if node.get("node_kind") == "canonical_claim_reference" and ref:
            out[ref] = node
    return out


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser()
    p.add_argument("--world", type=Path, required=True)
    p.add_argument("--evidence-manifest", type=Path, required=True)
    p.add_argument("--output-model", type=Path, required=True)
    p.add_argument("--output-sidecar", type=Path, required=True)
    return p.parse_args()


def main() -> int:
    args = parse_args()
    model = load(args.world)
    manifest = load(args.evidence_manifest)
    if model.get("schema_version") != TARGET_SCHEMA:
        raise SystemExit("unexpected CandidateWorldModel schema")
    if bool((model.get("metadata") or {}).get("semantic_promotion", False)):
        raise SystemExit("refusing semantically promoted world model")

    evidence_id = stable_source_id(manifest)
    if not evidence_id:
        raise SystemExit("evidence manifest missing Ibrahim stable_source_id")

    canonical = claim_nodes(model)
    out = copy.deepcopy(model)
    contractions: list[dict[str, Any]] = []
    attribution_paid = 0
    open_count = 0
    intermediate_count = 0

    for node in out.get("claims", []):
        if not isinstance(node, dict):
            continue
        kind = str(node.get("node_kind", ""))
        if kind not in {"canonical_claim_local_fragment", "intermediate_discourse_fragment"}:
            continue
        md = node.setdefault("metadata", {})
        residual = node.setdefault("residual", {})
        fragment_id = str(node.get("node_id", ""))
        claim_ref = str(md.get("claim_ref", ""))

        if kind == "intermediate_discourse_fragment" or not claim_ref:
            state = "not-applicable-intermediate"
            intermediate_count += 1
            current_source_id = ""
            speaker_status = ""
            paid = False
        else:
            cnode = canonical.get(claim_ref, {})
            cmd = cnode.get("metadata") or {}
            current_source_id = str(cmd.get("current_primary_source_stable_id", ""))
            speaker_status = str(cmd.get("current_primary_status", ""))
            paid = bool(current_source_id and current_source_id == evidence_id and speaker_status == "verified")
            state = "attribution-source-contracted" if paid else "evidence-open"
            attribution_paid += int(paid)
            open_count += int(not paid)

        receipt_id = f"fragment-evidence:{fragment_id}"
        md["fragment_evidence_contraction_ref"] = receipt_id
        residual["attribution_source_dimension"] = "paid" if paid else ("not-applicable" if kind == "intermediate_discourse_fragment" else "open")
        residual["whole_claim_extent_paid"] = False
        residual["claim_truth_promoted"] = False

        contractions.append({
            "receipt_id": receipt_id,
            "fragment_id": fragment_id,
            "fragment_kind": kind,
            "claim_ref": claim_ref,
            "contraction_state": state,
            "fragment_provenance_anchor_ids": list(node.get("source_anchor_ids") or []),
            "evidence_source_stable_id": evidence_id,
            "canonical_claim_primary_source_stable_id": current_source_id,
            "canonical_claim_primary_status": speaker_status,
            "attribution_source_paid": paid,
            "whole_claim_extent_paid": False,
            "claim_truth_promoted": False,
            "semantic_promotion": False,
        })

    out.setdefault("projections", []).append({
        "projection_id": SCHEMA,
        "projection_kind": "append_only_fragment_evidence_contraction",
        "status": "candidate",
        "evidence_source_stable_id": evidence_id,
        "sidecar": str(args.output_sidecar),
        "semantic_promotion": False,
    })
    out.setdefault("update_rules", []).append({
        "rule_id": "slr-fragment-evidence-append-only-v1",
        "rule_kind": "append_only_evidence_contraction",
        "description": "Evidence may contract a fragment dimension without rewriting fragment provenance, whole-claim extent, or claim truth.",
        "semantic_promotion": False,
    })
    meta = out.setdefault("metadata", {})
    meta["fragment_evidence_contraction"] = {
        "schema": SCHEMA,
        "evidence_source_stable_id": evidence_id,
        "fragment_provenance_is_evidence_authority": False,
        "evidence_authority_rewrites_fragment_provenance": False,
        "whole_claim_extent_paid": False,
        "claim_truth_promoted": False,
        "candidate_only": True,
        "semantic_promotion": False,
    }

    sidecar = {
        "schema": SCHEMA,
        "target_schema": TARGET_SCHEMA,
        "source_model_id": model.get("model_id", ""),
        "evidence_source_stable_id": evidence_id,
        "contractions": contractions,
        "summary": {
            "fragments": len(contractions),
            "attribution_source_paid": attribution_paid,
            "evidence_open": open_count,
            "intermediate_fragments": intermediate_count,
        },
        "fragment_provenance_is_evidence_authority": False,
        "evidence_authority_rewrites_fragment_provenance": False,
        "whole_claim_extent_paid": False,
        "claim_truth_promoted": False,
        "candidate_only": True,
        "semantic_promotion": False,
        "append_only": True,
    }

    args.output_model.parent.mkdir(parents=True, exist_ok=True)
    args.output_sidecar.parent.mkdir(parents=True, exist_ok=True)
    args.output_model.write_text(json.dumps(out, indent=2, ensure_ascii=False, sort_keys=True) + "\n", encoding="utf-8")
    args.output_sidecar.write_text(json.dumps(sidecar, indent=2, ensure_ascii=False, sort_keys=True) + "\n", encoding="utf-8")

    print(
        "SLR_FRAGMENT_EVIDENCE_CONTRACTION_RECEIPT "
        f"schema={SCHEMA} fragments={len(contractions)} attribution_source_paid={attribution_paid} "
        f"evidence_open={open_count} intermediate_fragments={intermediate_count} "
        "fragment_provenance_is_evidence_authority=false evidence_authority_rewrites_fragment_provenance=false "
        "whole_claim_extent_paid=false candidate_only=true semantic_promotion=false claim_truth_promoted=false append_only=true",
        file=sys.stderr,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
