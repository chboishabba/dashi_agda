#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

SCHEMA = "slr-world-research-typed-route-frontier-v1"


def load(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise SystemExit(f"expected JSON object: {path}")
    return value


def _route_obligation(action: dict[str, Any]) -> dict[str, Any]:
    return {
        "obligation_kind": "follow-related-qid",
        "qid": str(action.get("target_qid", "")),
        "cross_language_gap_coverage": int(action.get("cross_language_gap_coverage", 0) or 0),
        "source_surface_support": int(action.get("source_surface_support", 0) or 0),
        "root_qid_support": int(action.get("root_qid_support", 0) or 0),
        "typed_wikidata_property_target": bool(action.get("property_id")),
        "route_action_id": str(action.get("action_id", "")),
        "route_family": str(action.get("route_family", "")),
        "route_source_qid": str(action.get("source_qid", "")),
        "route_property_id": str(action.get("property_id", "")),
        "route_direction": str(action.get("route_direction", "")),
        "pareto_front_rank": int(action.get("pareto_front_rank", 0) or 0),
        "typed_route_preselected": True,
        "pareto_dimensions_scalarized": False,
        "frontier_rank_is_truth_rank": False,
        "candidate_only": True,
        "semantic_promotion": False,
    }


def weld_typed_route_frontier(
    iteration: dict[str, Any], closure: dict[str, Any], plan: dict[str, Any]
) -> dict[str, dict[str, Any]]:
    if iteration.get("schema") != "slr-world-research-iteration-v1":
        raise ValueError("unexpected iteration schema")
    if closure.get("schema") != "slr-semantic-world-closure-v1":
        raise ValueError("unexpected closure schema")

    missing = [
        dict(row)
        for row in iteration.get("next_acquisition_obligations") or []
        if isinstance(row, dict)
        and row.get("obligation_kind") == "missing-language-surface"
    ]
    routes = [
        _route_obligation(row)
        for row in plan.get("selected_route_actions") or []
        if isinstance(row, dict) and str(row.get("target_qid", "")).strip()
    ]
    obligations = missing + routes

    welded_closure = dict(closure)
    welded_closure["acquisition_obligations"] = obligations
    welded_closure["typed_route_frontier_locked"] = True
    welded_closure["pareto_support_coordinates_emitted"] = True
    welded_closure["typed_route_selection_rewrites_truth"] = False
    welded_closure["candidate_only"] = True
    welded_closure["semantic_promotion"] = False
    summary = dict(welded_closure.get("summary") or {})
    summary["acquisition_obligations"] = len(obligations)
    welded_closure["summary"] = summary

    welded_iteration = dict(iteration)
    welded_iteration["semantic_closure_reference"] = "__SYNTHETIC_TYPED_ROUTE_CLOSURE__"
    welded_iteration["next_acquisition_obligations"] = obligations
    welded_iteration["typed_route_frontier_locked"] = True
    welded_iteration["typed_route_selection_rewrites_truth"] = False
    welded_iteration["pareto_support_coordinates_emitted"] = True
    welded_iteration["pareto_dimensions_scalarized"] = False
    welded_iteration["candidate_only"] = True
    welded_iteration["semantic_promotion"] = False
    return {"closure": welded_closure, "iteration": welded_iteration}


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser()
    p.add_argument("--iteration", type=Path, required=True)
    p.add_argument("--closure", type=Path, required=True)
    p.add_argument("--plan", type=Path, required=True)
    p.add_argument("--output-closure", type=Path, required=True)
    p.add_argument("--output-iteration", type=Path, required=True)
    return p.parse_args()


def main() -> int:
    args = parse_args()
    welded = weld_typed_route_frontier(load(args.iteration), load(args.closure), load(args.plan))
    welded["iteration"]["semantic_closure_reference"] = str(args.output_closure)
    args.output_closure.parent.mkdir(parents=True, exist_ok=True)
    args.output_closure.write_text(json.dumps(welded["closure"], indent=2, sort_keys=True) + "\n", encoding="utf-8")
    args.output_iteration.write_text(json.dumps(welded["iteration"], indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(
        "SLR_TYPED_ROUTE_FRONTIER_WELD_RECEIPT "
        f"schema={SCHEMA} obligations={len(welded['closure'].get('acquisition_obligations') or [])} "
        "typed_route_frontier_locked=true typed_route_selection_rewrites_truth=false "
        "pareto_dimensions_scalarized=false candidate_only=true semantic_promotion=false"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
