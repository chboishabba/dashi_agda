#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import sys
from copy import deepcopy
from pathlib import Path
from typing import Any

SCHEMA = "slr-gwb-wikimedia-identity-contraction-v1"
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
        value = json.loads(raw)
        if not isinstance(value, dict):
            raise SystemExit(f"expected JSON object row in {path}")
        rows.append(value)
    return rows


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser()
    p.add_argument("--world-model", type=Path, required=True)
    p.add_argument("--seeds", type=Path, required=True)
    p.add_argument("--graph", type=Path, required=True)
    p.add_argument("--output-model", type=Path, required=True)
    p.add_argument("--output-sidecar", type=Path, required=True)
    return p.parse_args()


def main() -> int:
    args = parse_args()
    world = load(args.world_model)
    graph = load(args.graph)
    seeds = read_jsonl(args.seeds)

    if world.get("schema_version") != TARGET_SCHEMA:
        raise SystemExit(f"unexpected CandidateWorldModel schema: {world.get('schema_version')!r}")
    if bool((world.get("metadata") or {}).get("semantic_promotion", False)):
        raise SystemExit("refusing semantically promoted input")
    if graph.get("schema") != "slr-wikimedia-world-follow-v1":
        raise SystemExit(f"unexpected graph schema: {graph.get('schema')!r}")
    if bool(graph.get("semantic_promotion", False)):
        raise SystemExit("refusing semantically promoted graph")

    receipt_by_seed = {
        str(r.get("seed_id", "")): r
        for r in (graph.get("seed_receipts") or [])
        if isinstance(r, dict) and r.get("seed_id")
    }
    node_by_qid = {
        str(n.get("node_id", "")): n
        for n in (graph.get("nodes") or [])
        if isinstance(n, dict) and n.get("node_id")
    }

    contractions: list[dict[str, Any]] = []
    source_work_paid = 0
    source_work_unpaid = 0
    topic_anchor_paid = 0
    runtime_resolved_work_identities = 0

    for seed in sorted(seeds, key=lambda r: int(r.get("document_ordinal", -1))):
        ordinal = int(seed.get("document_ordinal", -1))
        seed_id = str(seed.get("seed_id", ""))
        scope = str(seed.get("identity_scope", ""))
        role = str(seed.get("coordinate_role", ""))
        seed_receipt = receipt_by_seed.get(seed_id, {})
        candidates = [
            c for c in (seed_receipt.get("candidate_qids") or [])
            if isinstance(c, dict) and c.get("id")
        ]
        paid_candidates = [c for c in candidates if bool(c.get("identity_paid", False))]

        exact_source_work = False
        qid = ""
        basis = ""
        if scope == "exact-work-identity":
            expected = str(seed.get("qid", ""))
            match = next((c for c in paid_candidates if str(c.get("id", "")) == expected), None)
            if match is not None:
                exact_source_work = True
                qid = expected
                basis = str(match.get("match_basis", "reviewed-explicit-qid"))
        elif scope == "explicit-wikipedia-work-title-qid-runtime-resolved":
            if len(paid_candidates) == 1:
                match = paid_candidates[0]
                if str(match.get("match_basis", "")) == "explicit-wikipedia-title":
                    exact_source_work = True
                    qid = str(match.get("id", ""))
                    basis = "explicit-wikipedia-title-runtime-resolved"
                    runtime_resolved_work_identities += 1

        topic_anchor = role in {"subject-person", "topic-family"}
        if exact_source_work:
            source_work_paid += 1
        else:
            source_work_unpaid += 1
        if topic_anchor and paid_candidates:
            topic_anchor_paid += 1

        node = node_by_qid.get(qid, {}) if qid else {}
        contractions.append({
            "schema": SCHEMA,
            "document_ordinal": ordinal,
            "seed_id": seed_id,
            "coordinate_role": role,
            "identity_scope": scope,
            "source_work_identity_status": "paid" if exact_source_work else "unpaid",
            "source_work_qid": qid,
            "source_work_label": str(node.get("label", "")) if qid else "",
            "payment_basis": basis,
            "topic_anchor_status": "paid" if topic_anchor and paid_candidates else "not-applicable",
            "topic_anchor_qids": [str(c.get("id", "")) for c in paid_candidates] if topic_anchor else [],
            "topic_anchor_is_source_object_identity": False,
            "claim_truth_promoted": False,
            "candidate_only": True,
            "semantic_promotion": False,
        })

    sidecar = {
        "schema": SCHEMA,
        "source_world_model_id": world.get("model_id", ""),
        "source_graph_schema": graph.get("schema", ""),
        "contractions": contractions,
        "summary": {
            "documents": len(contractions),
            "source_work_identity_paid": source_work_paid,
            "source_work_identity_unpaid": source_work_unpaid,
            "topic_anchor_paid": topic_anchor_paid,
            "runtime_resolved_work_identities": runtime_resolved_work_identities,
        },
        "topic_anchor_is_source_object_identity": False,
        "wikimedia_identity_creates_claim_truth": False,
        "candidate_only": True,
        "semantic_promotion": False,
    }

    out = deepcopy(world)
    provenance = out.get("provenance_graph") or []
    by_ordinal = {int(c["document_ordinal"]): c for c in contractions}
    for record in provenance:
        if not isinstance(record, dict):
            continue
        ordinal = record.get("document_ordinal")
        if ordinal is None:
            continue
        contraction = by_ordinal.get(int(ordinal))
        if contraction is not None:
            record["wikimedia_identity_contraction"] = {
                "schema": SCHEMA,
                "source_work_identity_status": contraction["source_work_identity_status"],
                "source_work_qid": contraction["source_work_qid"],
                "source_work_label": contraction["source_work_label"],
                "payment_basis": contraction["payment_basis"],
                "topic_anchor_status": contraction["topic_anchor_status"],
                "topic_anchor_qids": contraction["topic_anchor_qids"],
                "topic_anchor_is_source_object_identity": False,
                "semantic_promotion": False,
            }

    out.setdefault("projections", []).append({
        "projection_id": SCHEMA,
        "projection_kind": "gwb_wikimedia_identity_residual_contraction",
        "status": "candidate",
        "sidecar": str(args.output_sidecar),
        "source_work_identity_paid": source_work_paid,
        "source_work_identity_unpaid": source_work_unpaid,
        "claim_truth_promoted": False,
        "semantic_promotion": False,
    })
    metadata = out.setdefault("metadata", {})
    metadata["gwb_wikimedia_identity_contraction"] = {
        "schema": SCHEMA,
        "sidecar": str(args.output_sidecar),
        **sidecar["summary"],
        "topic_anchor_is_source_object_identity": False,
        "wikimedia_identity_creates_claim_truth": False,
        "candidate_only": True,
        "semantic_promotion": False,
    }
    metadata["candidate_only"] = True
    metadata["semantic_promotion"] = False

    args.output_sidecar.parent.mkdir(parents=True, exist_ok=True)
    args.output_model.parent.mkdir(parents=True, exist_ok=True)
    args.output_sidecar.write_text(json.dumps(sidecar, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    args.output_model.write_text(json.dumps(out, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    print(
        "SLR_GWB_WIKIMEDIA_IDENTITY_CONTRACTION_RECEIPT "
        f"schema={SCHEMA} documents={len(contractions)} "
        f"source_work_identity_paid={source_work_paid} "
        f"source_work_identity_unpaid={source_work_unpaid} "
        f"topic_anchor_paid={topic_anchor_paid} "
        f"runtime_resolved_work_identities={runtime_resolved_work_identities} "
        "topic_anchor_is_source_object_identity=false wikimedia_identity_creates_claim_truth=false "
        "candidate_only=true semantic_promotion=false",
        file=sys.stderr,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
