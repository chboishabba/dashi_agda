#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

SCHEMA = "slr-world-research-budget-v1"


def load(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise SystemExit(f"expected JSON object: {path}")
    return value


def _dedupe_missing(rows: list[dict[str, Any]]) -> list[dict[str, Any]]:
    seen: set[tuple[str, str]] = set()
    out: list[dict[str, Any]] = []
    for row in sorted(rows, key=lambda r: (str(r.get("qid", "")), str(r.get("language", "")))):
        key = (str(row.get("qid", "")), str(row.get("language", "")))
        if not all(key) or key in seen:
            continue
        seen.add(key)
        out.append(dict(row))
    return out


def _dedupe_related(rows: list[dict[str, Any]]) -> list[dict[str, Any]]:
    seen: set[str] = set()
    out: list[dict[str, Any]] = []
    for row in sorted(rows, key=lambda r: str(r.get("qid", ""))):
        qid = str(row.get("qid", ""))
        if not qid or qid in seen:
            continue
        seen.add(qid)
        out.append(dict(row))
    return out


def plan_frontier(
    obligations: list[dict[str, Any]],
    *,
    max_new_qids: int,
    max_missing_surfaces: int,
) -> dict[str, Any]:
    if max_new_qids < 0 or max_missing_surfaces < 0:
        raise ValueError("budgets must be non-negative")
    clean = [dict(x) for x in obligations if isinstance(x, dict) and bool(x.get("candidate_only", True))]
    missing = _dedupe_missing([x for x in clean if x.get("obligation_kind") == "missing-language-surface"])
    related = _dedupe_related([x for x in clean if x.get("obligation_kind") == "follow-related-qid"])
    selected_missing = missing[:max_missing_surfaces]
    selected_related = related[:max_new_qids]
    selected_count = len(selected_missing) + len(selected_related)
    if not clean:
        stop_reason = "frontier-empty"
    elif selected_count == 0:
        stop_reason = "budget-exhausted-before-acquisition"
    elif len(selected_missing) == len(missing) and len(selected_related) == len(related):
        stop_reason = "selected-entire-frontier"
    else:
        stop_reason = "budget-limited-selection"
    return {
        "schema": SCHEMA,
        "selected_missing_surfaces": selected_missing,
        "selected_related_qids": selected_related,
        "unselected_missing_surfaces": missing[max_missing_surfaces:],
        "unselected_related_qids": related[max_new_qids:],
        "stop_reason": stop_reason,
        "consumer_closure_paid": False,
        "budget_exhaustion_is_consumer_closure": False,
        "frontier_rank_is_truth_rank": False,
        "candidate_only": True,
        "semantic_promotion": False,
        "summary": {
            "input_obligations": len(clean),
            "deduplicated_missing_surfaces": len(missing),
            "deduplicated_follow_related_qids": len(related),
            "selected_missing_surfaces": len(selected_missing),
            "selected_related_qids": len(selected_related),
            "remaining_missing_surfaces": max(0, len(missing) - len(selected_missing)),
            "remaining_related_qids": max(0, len(related) - len(selected_related)),
            "max_new_qids": max_new_qids,
            "max_missing_surfaces": max_missing_surfaces,
        },
    }


def seed_rows(plan: dict[str, Any], *, iteration_index: int) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for rank, obligation in enumerate(plan.get("selected_related_qids") or [], start=1):
        qid = str(obligation.get("qid", ""))
        if not qid:
            continue
        rows.append({
            "seed_id": f"world-research-iteration-{iteration_index}-qid-{rank}",
            "seed_state": "budgeted-follow-related-qid",
            "qid": qid,
            "coordinate_role": "semantic-gap-next-acquisition",
            "identity_scope": "explicit-related-qid",
            "candidate_only": True,
            "semantic_promotion": False,
        })
    return rows


def merge_graphs(base: dict[str, Any], delta: dict[str, Any]) -> dict[str, Any]:
    if base.get("schema") != "slr-wikimedia-world-follow-v1" or delta.get("schema") != "slr-wikimedia-world-follow-v1":
        raise ValueError("graph schema mismatch")

    def uniq_rows(rows: list[dict[str, Any]], key_fn) -> list[dict[str, Any]]:
        seen: set[Any] = set()
        out: list[dict[str, Any]] = []
        for row in rows:
            if not isinstance(row, dict):
                continue
            key = key_fn(row)
            if key in seen:
                continue
            seen.add(key)
            out.append(row)
        return out

    nodes = uniq_rows(
        list(base.get("nodes") or []) + list(delta.get("nodes") or []),
        lambda r: str(r.get("node_id", "")),
    )
    edges = uniq_rows(
        list(base.get("item_property_edges") or []) + list(delta.get("item_property_edges") or []),
        lambda r: (str(r.get("source", "")), str(r.get("property_id", "")), str(r.get("target", "")), str(r.get("edge_class", ""))),
    )
    seeds = uniq_rows(
        list(base.get("seed_receipts") or []) + list(delta.get("seed_receipts") or []),
        lambda r: (str(r.get("seed_id", "")), json.dumps(r.get("candidate_qids") or [], sort_keys=True)),
    )
    first = uniq_rows(
        list(base.get("first_link_candidates") or []) + list(delta.get("first_link_candidates") or []),
        lambda r: (str(r.get("from_qid", "")), str(r.get("candidate_qid", "")), str(r.get("candidate_title", ""))),
    )
    pages = dict(base.get("wikipedia_pages") or {})
    pages.update(delta.get("wikipedia_pages") or {})
    parent_edges = sum(1 for e in edges if e.get("edge_class") == "parent")
    related_edges = len(edges) - parent_edges
    transport = {
        "kind": "merged-budgeted-world-research",
        "base_transport": base.get("transport") or {},
        "delta_transport": delta.get("transport") or {},
        "transport_provenance_is_entity_identity": False,
    }
    return {
        "schema": "slr-wikimedia-world-follow-v1",
        "source_world_model_id": base.get("source_world_model_id") or delta.get("source_world_model_id", ""),
        "seed_receipts": seeds,
        "nodes": nodes,
        "item_property_edges": edges,
        "wikipedia_pages": pages,
        "first_link_candidates": first,
        "routing_policy": dict(base.get("routing_policy") or delta.get("routing_policy") or {}),
        "transport": transport,
        "summary": {
            "input_seed_count": len(seeds),
            "unresolved_seed_count": 0,
            "qid_node_count": len(nodes),
            "item_property_edge_count": len(edges),
            "parent_edge_count": parent_edges,
            "surrounding_or_related_edge_count": related_edges,
            "wikipedia_page_count": len(pages),
            "first_link_candidate_count": len(first),
            "first_link_follow_count": sum(1 for x in first if x.get("candidate_qid")),
        },
        "candidate_only": True,
        "semantic_promotion": False,
    }


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser()
    sub = p.add_subparsers(dest="command", required=True)

    plan = sub.add_parser("plan")
    plan.add_argument("--iteration", type=Path, required=True)
    plan.add_argument("--output", type=Path, required=True)
    plan.add_argument("--seeds", type=Path, required=True)
    plan.add_argument("--iteration-index", type=int, default=1)
    plan.add_argument("--max-new-qids", type=int, default=8)
    plan.add_argument("--max-missing-surfaces", type=int, default=4)

    merge = sub.add_parser("merge")
    merge.add_argument("--base-graph", type=Path, required=True)
    merge.add_argument("--delta-graph", type=Path, required=True)
    merge.add_argument("--output", type=Path, required=True)

    sub.add_parser("self-check")
    return p.parse_args()


def self_check() -> int:
    plan = plan_frontier(
        [
            {"obligation_kind": "follow-related-qid", "qid": "Q2", "candidate_only": True},
            {"obligation_kind": "follow-related-qid", "qid": "Q2", "candidate_only": True},
            {"obligation_kind": "missing-language-surface", "qid": "Q1", "language": "fr", "candidate_only": True},
        ],
        max_new_qids=1,
        max_missing_surfaces=1,
    )
    assert plan["summary"]["deduplicated_follow_related_qids"] == 1
    assert len(seed_rows(plan, iteration_index=1)) == 1
    assert plan["consumer_closure_paid"] is False
    print(
        "SLR_WORLD_RESEARCH_BUDGET_SELF_CHECK schema=slr-world-research-budget-v1 passed=true "
        "frontier_rank_is_truth_rank=false budget_exhaustion_is_consumer_closure=false semantic_promotion=false",
        file=sys.stderr,
    )
    return 0


def main() -> int:
    args = parse_args()
    if args.command == "self-check":
        return self_check()
    if args.command == "plan":
        iteration = load(args.iteration)
        if iteration.get("schema") != "slr-world-research-iteration-v1":
            raise SystemExit(f"unexpected iteration schema: {iteration.get('schema')!r}")
        if bool(iteration.get("semantic_promotion", False)):
            raise SystemExit("refusing semantically promoted iteration")
        plan = plan_frontier(
            [x for x in iteration.get("next_acquisition_obligations") or [] if isinstance(x, dict)],
            max_new_qids=args.max_new_qids,
            max_missing_surfaces=args.max_missing_surfaces,
        )
        plan["source_iteration_schema"] = iteration.get("schema", "")
        plan["iteration_index"] = args.iteration_index
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(plan, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        rows = seed_rows(plan, iteration_index=args.iteration_index)
        args.seeds.parent.mkdir(parents=True, exist_ok=True)
        args.seeds.write_text("".join(json.dumps(row, sort_keys=True) + "\n" for row in rows), encoding="utf-8")
        s = plan["summary"]
        print(
            "SLR_WORLD_RESEARCH_BUDGET_RECEIPT "
            f"schema={SCHEMA} input={s['input_obligations']} selected_missing_surfaces={s['selected_missing_surfaces']} "
            f"selected_related_qids={s['selected_related_qids']} remaining_missing_surfaces={s['remaining_missing_surfaces']} "
            f"remaining_related_qids={s['remaining_related_qids']} stop_reason={plan['stop_reason']} "
            "frontier_rank_is_truth_rank=false budget_exhaustion_is_consumer_closure=false "
            "candidate_only=true semantic_promotion=false",
            file=sys.stderr,
        )
        return 0
    if args.command == "merge":
        merged = merge_graphs(load(args.base_graph), load(args.delta_graph))
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(merged, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        print(
            "SLR_WORLD_RESEARCH_GRAPH_MERGE_RECEIPT schema=slr-wikimedia-world-follow-v1 "
            f"qid_nodes={merged['summary']['qid_node_count']} property_edges={merged['summary']['item_property_edge_count']} "
            "candidate_only=true semantic_promotion=false",
            file=sys.stderr,
        )
        return 0
    raise SystemExit("unknown command")


if __name__ == "__main__":
    raise SystemExit(main())
