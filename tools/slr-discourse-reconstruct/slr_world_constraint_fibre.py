#!/usr/bin/env python3
from __future__ import annotations

import argparse
import copy
import json
import sys
from pathlib import Path
from typing import Any

SCHEMA = "slr-world-constraint-fibre-v1"
TARGET_SCHEMA = "sl.candidate_world_model.v0_1"


def load_json(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise SystemExit(f"expected JSON object: {path}")
    return value


def source_coordinates(manifest: dict[str, Any]) -> dict[str, Any]:
    ibrahim = manifest.get("ibrahim") or {}
    doi = ibrahim.get("doi") or {}
    return {
        "source_schema": manifest.get("schema", ""),
        "source_title": manifest.get("title", ""),
        "publisher": manifest.get("publisher", ""),
        "published_date": manifest.get("published_date", ""),
        "source_role": manifest.get("source_role", ""),
        "stable_source_id": ibrahim.get("stable_source_id", ""),
        "dewey_parent": ibrahim.get("dewey_parent", ""),
        "dewey_role": ibrahim.get("dewey_role", ""),
        "doi_state": doi.get("state", ""),
        "doi_scope": doi.get("scope", ""),
        "qid_role": ibrahim.get("qid_role", ""),
        "verified_qids": ibrahim.get("verified_qids", {}),
        "unresolved_qids": ibrahim.get("unresolved_qids", []),
        "primary_for": (manifest.get("source_role_by_claim") or {}).get("primary_for", []),
        "not_automatically_primary_for": (manifest.get("source_role_by_claim") or {}).get(
            "not_automatically_primary_for", []
        ),
        "acquisition_order_can_be_opportunistic": bool(
            ibrahim.get("acquisition_order_can_be_opportunistic", False)
        ),
        "payment_order_requires_same_object_and_claim_role_weld": bool(
            ibrahim.get("payment_order_requires_same_object_and_claim_role_weld", False)
        ),
    }


def dimension(status: str, reference: Any, note: str) -> dict[str, Any]:
    return {"status": status, "reference": reference, "note": note}


def claim_fibre(claim: dict[str, Any], coords: dict[str, Any]) -> dict[str, Any]:
    node_id = str(claim.get("node_id", ""))
    kind = str(claim.get("node_kind", ""))
    residual = claim.get("residual") or {}
    metadata = claim.get("metadata") or {}
    conflict_ids = list(claim.get("conflict_ids") or [])
    pareto = list(residual.get("pareto_fibres") or [])
    pnf_residual_count = int(residual.get("pnf_residual_count") or 0)
    false_cut = bool(residual.get("false_cut_risk", False))
    hidden_splice = bool(residual.get("hidden_speaker_splice_risk", False))

    if kind == "discourse_boundary_candidate":
        projection = metadata.get("projection", "unresolved")
        hard_admit = bool(metadata.get("hard_cut_admissible", False))
        discourse_status = "resolved-candidate" if projection != "unresolved" else "residual-fibre"
        role_status = "admitted" if hard_admit else ("vetoed" if false_cut else "unresolved")
        role_ref = {
            "crossing_roles": metadata.get("crossing_roles", []),
            "actor_crossing": bool(metadata.get("actor_crossing", False)),
            "patient_crossing": bool(metadata.get("patient_crossing", False)),
            "clause_crossing": bool(metadata.get("clause_crossing", False)),
            "coordination_crossing": bool(metadata.get("coordination_crossing", False)),
            "predicate_aux_crossing": bool(metadata.get("predicate_aux_crossing", False)),
            "hard_cut_admissible": hard_admit,
        }
    else:
        projection = metadata.get("boundary_projection", "")
        discourse_status = "span-candidate"
        role_status = "carried"
        role_ref = {
            "actor_crossing": bool(metadata.get("actor_crossing", False)),
            "patient_crossing": bool(metadata.get("patient_crossing", False)),
            "clause_crossing": bool(metadata.get("clause_crossing", False)),
            "coordination_crossing": bool(metadata.get("coordination_crossing", False)),
            "predicate_aux_crossing": bool(metadata.get("predicate_aux_crossing", False)),
        }

    compatible = not false_cut
    state = "vetoed" if false_cut else ("conflicted" if conflict_ids else "candidate-compatible")
    return {
        "candidate_id": node_id,
        "candidate_kind": kind,
        "constraint_state": state,
        "compatible": compatible,
        "candidate_only": True,
        "truth_promoted": False,
        "dimensions": {
            "discourse": dimension(
                discourse_status,
                {"projection": projection, "pareto_fibres": pareto},
                "Discourse projection and residual alternatives are retained without scalar collapse.",
            ),
            "pnf": dimension(
                "residual-observed" if pnf_residual_count else "no-local-residual-observed",
                {"pnf_residual_count": pnf_residual_count},
                "PNF residual count is a constraint coordinate, not a truth or quality score.",
            ),
            "role": dimension(
                role_status,
                role_ref,
                "Actor/patient/clause/predicate-aux compatibility is consumer-specific; coordination alone is nonfatal.",
            ),
            "source_attribution": dimension(
                "source-object-attached",
                {
                    "source_anchor_ids": claim.get("source_anchor_ids", []),
                    "stable_source_id": coords.get("stable_source_id", ""),
                    "source_role": coords.get("source_role", ""),
                },
                "Source-object identity and claim-relative primaryness do not by themselves verify candidate semantics.",
            ),
            "temporal": dimension(
                "source-date-bounded",
                {"published_date": coords.get("published_date", "")},
                "Publication date is retained; utterance/event-time identity requires a separate receipt when needed.",
            ),
            "narrative": dimension(
                "alternatives-retained" if conflict_ids or hidden_splice else "no-local-conflict-observed",
                {"conflict_ids": conflict_ids, "hidden_speaker_splice_risk": hidden_splice},
                "Narrative alternatives remain live until source/review evidence contracts the fibre.",
            ),
            "authority": dimension(
                "claim-relative-primary-scope-attached",
                {
                    "primary_for": coords.get("primary_for", []),
                    "not_automatically_primary_for": coords.get("not_automatically_primary_for", []),
                    "dewey_parent": coords.get("dewey_parent", ""),
                    "dewey_role": coords.get("dewey_role", ""),
                    "doi_state": coords.get("doi_state", ""),
                    "qid_role": coords.get("qid_role", ""),
                },
                "Dewey/QID/DOI/link coordinates are provenance/retrieval/identity coordinates and do not manufacture authority.",
            ),
        },
        "promotion_receipt_reference": "unpaid:review/promote/abstain",
    }


def relation_fibre(relation: dict[str, Any], coords: dict[str, Any]) -> dict[str, Any]:
    rid = str(relation.get("relation_id", ""))
    metadata = relation.get("metadata") or {}
    residual = relation.get("residual") or {}
    core_crossing = any(
        bool(metadata.get(name, False))
        for name in ("actor_crossing", "patient_crossing", "clause_crossing", "predicate_aux_crossing")
    )
    return {
        "candidate_id": rid,
        "candidate_kind": "relation",
        "constraint_state": "consumer-vetoed" if core_crossing else "candidate-compatible",
        "compatible": not core_crossing,
        "candidate_only": True,
        "truth_promoted": False,
        "dimensions": {
            "discourse": dimension(
                "candidate-relation",
                {
                    "relation_kind": relation.get("relation_kind", ""),
                    "pareto_fibres": residual.get("pareto_fibres", []),
                },
                "Relation is a candidate projection of the admitted reconstruction, not a world fact.",
            ),
            "pnf": dimension(
                "carried-from-boundary",
                {},
                "PNF topology remains owned by the boundary/span source tables.",
            ),
            "role": dimension(
                "vetoed" if core_crossing else "preserved",
                metadata,
                "Core role crossings veto a hard relation consumer; coordination alone does not.",
            ),
            "source_attribution": dimension(
                "source-object-attached",
                {
                    "source_anchor_ids": relation.get("source_anchor_ids", []),
                    "stable_source_id": coords.get("stable_source_id", ""),
                },
                "Same source object retained append-only.",
            ),
            "temporal": dimension(
                "source-date-bounded",
                {"published_date": coords.get("published_date", "")},
                "No event-time claim is promoted.",
            ),
            "narrative": dimension(
                "candidate",
                {},
                "Alternative relation interpretations may be added without rewriting this candidate.",
            ),
            "authority": dimension(
                "claim-relative-primary-scope-attached",
                {
                    "primary_for": coords.get("primary_for", []),
                    "not_automatically_primary_for": coords.get("not_automatically_primary_for", []),
                },
                "Primaryness is claim-relative and does not imply causal/legal authority.",
            ),
        },
        "promotion_receipt_reference": "unpaid:review/promote/abstain",
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--world-model", type=Path, required=True)
    parser.add_argument("--source-manifest", type=Path, required=True)
    parser.add_argument("--output-model", type=Path, required=True)
    parser.add_argument("--output-fibres", type=Path, required=True)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    model = load_json(args.world_model)
    manifest = load_json(args.source_manifest)
    if model.get("schema_version") != TARGET_SCHEMA:
        raise SystemExit(f"unexpected world model schema: {model.get('schema_version')}")
    if model.get("model_status") != "candidate":
        raise SystemExit("world constraint attachment only accepts candidate models")
    if bool((model.get("metadata") or {}).get("semantic_promotion", False)):
        raise SystemExit("refusing to attach constraints to semantically promoted model")

    coords = source_coordinates(manifest)
    fibres = [claim_fibre(row, coords) for row in model.get("claims", [])]
    fibres.extend(relation_fibre(row, coords) for row in model.get("relations", []))
    by_id = {row["candidate_id"]: row for row in fibres}

    constrained = copy.deepcopy(model)
    for row in constrained.get("claims", []):
        cid = row.get("node_id", "")
        if cid in by_id:
            row["world_constraint_ref"] = f"world-constraint:{cid}"
    for row in constrained.get("relations", []):
        cid = row.get("relation_id", "")
        if cid in by_id:
            row["world_constraint_ref"] = f"world-constraint:{cid}"

    constrained.setdefault("projections", []).append(
        {
            "projection_id": "slr-world-constraint-fibre-v1",
            "projection_kind": "typed_world_constraint_fibre",
            "status": "candidate",
            "source_model_id": model.get("model_id", ""),
            "sidecar": str(args.output_fibres),
            "scalar_score": False,
            "semantic_promotion": False,
        }
    )
    constrained.setdefault("update_rules", []).append(
        {
            "rule_id": "slr-world-constraint-append-only-v1",
            "rule_kind": "append_only_constraint_refinement",
            "description": "New source/DOI/QID/temporal/narrative/legal evidence may contract or reopen candidate fibres through new receipts; prior source state is not rewritten.",
            "semantic_promotion": False,
        }
    )
    metadata = constrained.setdefault("metadata", {})
    metadata["world_constraint_status"] = "attached-candidate-only"
    metadata["world_constraint_schema"] = SCHEMA
    metadata["world_constraint_sidecar"] = str(args.output_fibres)
    metadata["world_constraint_scalar_score"] = False
    metadata["semantic_promotion"] = False
    metadata["candidate_only"] = True

    sidecar = {
        "schema": SCHEMA,
        "target_schema": TARGET_SCHEMA,
        "source_model_id": model.get("model_id", ""),
        "source_coordinates": coords,
        "constraint_fibres": fibres,
        "summary": {
            "candidate_count": len(fibres),
            "compatible_count": sum(bool(row["compatible"]) for row in fibres),
            "vetoed_count": sum(not bool(row["compatible"]) for row in fibres),
            "conflicted_count": sum(row["constraint_state"] == "conflicted" for row in fibres),
        },
        "candidate_only": True,
        "semantic_promotion": False,
        "scalar_score": False,
        "append_only": True,
    }

    args.output_fibres.parent.mkdir(parents=True, exist_ok=True)
    args.output_model.parent.mkdir(parents=True, exist_ok=True)
    args.output_fibres.write_text(json.dumps(sidecar, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    args.output_model.write_text(json.dumps(constrained, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(
        "SLR_WORLD_CONSTRAINT_FIBRE_RECEIPT "
        f"schema={SCHEMA} target={TARGET_SCHEMA} model_id={model.get('model_id','')} "
        f"candidates={len(fibres)} compatible={sidecar['summary']['compatible_count']} "
        f"vetoed={sidecar['summary']['vetoed_count']} conflicted={sidecar['summary']['conflicted_count']} "
        "scalar_score=false append_only=true candidate_only=true semantic_promotion=false",
        file=sys.stderr,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
