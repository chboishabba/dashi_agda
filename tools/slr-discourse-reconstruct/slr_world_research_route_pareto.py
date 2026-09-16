#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import sys
from collections import defaultdict
from pathlib import Path
from typing import Any

SCHEMA = "slr-world-research-route-pareto-v1"
HISTORY_SCHEMA = "slr-world-research-route-yield-history-v1"

ROUTE_PROPERTY_FAMILY = {
    "P31": ("wikidata-instance-class", 5, "outbound", True),
    "P279": ("wikidata-subclass-parent", 5, "outbound", True),
    "P361": ("wikidata-part-of", 4, "outbound", True),
    "P527": ("wikidata-has-part", 4, "outbound", True),
    "P131": ("wikidata-admin-location", 3, "outbound", False),
    "P17": ("wikidata-country", 3, "outbound", False),
    "P1269": ("wikidata-facet-of", 3, "outbound", False),
}

# Higher is better except the two explicit cost/burden dimensions.
PARETO_AXES: tuple[tuple[str, str], ...] = (
    ("cross_language_gap_coverage", "max"),
    ("source_surface_support", "max"),
    ("root_qid_support", "max"),
    ("typed_property_support", "max"),
    ("route_specificity", "max"),
    ("yield_history_observed", "max"),
    ("prior_contracted_old_gaps", "max"),
    ("prior_retired_obligations", "max"),
    ("prior_new_gap_atoms", "min"),
    ("prior_network_requests", "min"),
)


def load(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise SystemExit(f"expected JSON object: {path}")
    return value


def _route_for_property(pid: str) -> tuple[str, int, str, bool]:
    return ROUTE_PROPERTY_FAMILY.get(pid, ("wikidata-property", 2, "outbound", False))


def _history_row(history: dict[str, Any] | None, route_family: str) -> dict[str, int]:
    row = (((history or {}).get("route_families") or {}).get(route_family) or {})
    trusted = int(row.get("trusted_single_family_rounds", 0) or 0)
    return {
        "yield_history_observed": 1 if trusted > 0 else 0,
        "prior_contracted_old_gaps": int(row.get("contracted_old_gaps", 0) or 0) if trusted else 0,
        "prior_retired_obligations": int(row.get("retired_obligations", 0) or 0) if trusted else 0,
        "prior_new_gap_atoms": int(row.get("new_gap_atoms", 0) or 0) if trusted else 0,
        "prior_network_requests": int(row.get("network_requests", 0) or 0) if trusted else 0,
    }


def _obligation_by_target(closure: dict[str, Any]) -> dict[str, dict[str, Any]]:
    out: dict[str, dict[str, Any]] = {}
    for row in closure.get("acquisition_obligations") or []:
        if not isinstance(row, dict) or row.get("obligation_kind") != "follow-related-qid":
            continue
        qid = str(row.get("qid", "")).strip()
        if qid:
            out[qid] = dict(row)
    return out


def _base_action(obligation: dict[str, Any], *, source_qid: str, target_qid: str, route_family: str,
                 route_specificity: int, route_direction: str, property_id: str = "",
                 hotspot_sensitive: bool = False, history: dict[str, Any] | None = None) -> dict[str, Any]:
    hist = _history_row(history, route_family)
    return {
        "action_id": f"{source_qid}:{property_id or route_family}:{target_qid}",
        "source_qid": source_qid,
        "property_id": property_id,
        "target_qid": target_qid,
        "qid": target_qid,
        "route_family": route_family,
        "route_direction": route_direction,
        "cross_language_gap_coverage": int(obligation.get("cross_language_gap_coverage", 0) or 0),
        "source_surface_support": int(obligation.get("source_surface_support", 0) or 0),
        "root_qid_support": int(obligation.get("root_qid_support", 0) or 0),
        "typed_property_support": 1 if property_id else 0,
        "route_specificity": int(route_specificity),
        **hist,
        "sensiblaw_hotspot_sensitive": bool(hotspot_sensitive),
        "sensiblaw_control_plane_only": True,
        "typed_property_is_claim_truth": False,
        "route_creates_claim_truth": False,
        "qid_identity_is_ontology_transplant": False,
        "provider_transport_is_entity_identity": False,
        "pareto_dimensions_scalarized": False,
        "frontier_rank_is_truth_rank": False,
        "candidate_only": True,
        "semantic_promotion": False,
    }


def build_route_actions(closure: dict[str, Any], graph: dict[str, Any], yield_history: dict[str, Any] | None) -> list[dict[str, Any]]:
    if closure.get("schema") != "slr-semantic-world-closure-v1":
        raise ValueError("unexpected semantic closure schema")
    if graph.get("schema") != "slr-wikimedia-world-follow-v1":
        raise ValueError("unexpected Wikimedia graph schema")
    obligations = _obligation_by_target(closure)
    actions: list[dict[str, Any]] = []
    covered: set[str] = set()

    for edge in graph.get("item_property_edges") or []:
        if not isinstance(edge, dict):
            continue
        target = str(edge.get("target", "")).strip()
        source = str(edge.get("source", "")).strip()
        pid = str(edge.get("property_id", "")).strip()
        if target not in obligations or not source or not pid:
            continue
        family, specificity, direction, hotspot = _route_for_property(pid)
        action = _base_action(
            obligations[target], source_qid=source, target_qid=target,
            route_family=family, route_specificity=specificity,
            route_direction=direction, property_id=pid,
            hotspot_sensitive=hotspot, history=yield_history,
        )
        if pid in {"P31", "P279"}:
            action["sensiblaw_diagnostic_family"] = "mixed-order/scc/metaclass-control-plane"
        elif pid in {"P361", "P527"}:
            action["sensiblaw_diagnostic_family"] = "parthood-typing-control-plane"
        else:
            action["sensiblaw_diagnostic_family"] = "typed-property-enrichment"
        actions.append(action)
        covered.add(target)

    for row in graph.get("first_link_candidates") or []:
        if not isinstance(row, dict):
            continue
        target = str(row.get("candidate_qid", "")).strip()
        source = str(row.get("from_qid", "")).strip()
        if target not in obligations or not source:
            continue
        action = _base_action(
            obligations[target], source_qid=source, target_qid=target,
            route_family="wikipedia-first-link", route_specificity=2,
            route_direction="outbound", hotspot_sensitive=False,
            history=yield_history,
        )
        action["ibrahim_parser_equivalence_paid"] = bool(row.get("ibrahim_parser_equivalence_paid", False))
        action["historical_snapshot_identity_paid"] = bool(row.get("historical_snapshot_identity_paid", False))
        action["current_first_link_is_historical_ibrahim_edge"] = False
        actions.append(action)
        covered.add(target)

    # A generic Wikipedia-related route remains admissible as the least
    # specific fallback.  It cannot dominate a typed route merely by existing.
    sources_by_target: dict[str, set[str]] = defaultdict(set)
    for atom in closure.get("canonical_atoms") or []:
        if not isinstance(atom, dict) or atom.get("kind") != "wiki-link":
            continue
        target = str(atom.get("object_qid", "")).strip()
        source = str(atom.get("subject_qid", "")).strip()
        if target in obligations and source:
            sources_by_target[target].add(source)
    for target, obligation in obligations.items():
        if target in covered:
            continue
        sources = sorted(sources_by_target.get(target) or {"unknown-root"})
        for source in sources:
            actions.append(_base_action(
                obligation, source_qid=source, target_qid=target,
                route_family="wikipedia-related", route_specificity=1,
                route_direction="outbound", hotspot_sensitive=False,
                history=yield_history,
            ))

    # Stable de-duplication by action identity.
    unique: dict[str, dict[str, Any]] = {}
    for action in actions:
        unique.setdefault(str(action["action_id"]), action)
    return [unique[key] for key in sorted(unique)]


def _value(row: dict[str, Any], field: str) -> int:
    return int(row.get(field, 0) or 0)


def _dominates(left: dict[str, Any], right: dict[str, Any]) -> bool:
    weak = True
    strict = False
    for field, direction in PARETO_AXES:
        a = _value(left, field)
        b = _value(right, field)
        if direction == "max":
            if a < b:
                weak = False
                break
            strict = strict or a > b
        else:
            if a > b:
                weak = False
                break
            strict = strict or a < b
    return weak and strict


def pareto_rank_actions(rows: list[dict[str, Any]]) -> list[dict[str, Any]]:
    remaining = [dict(row) for row in rows]
    ranked: list[dict[str, Any]] = []
    front_rank = 0
    while remaining:
        front = [
            row for row in remaining
            if not any(other is not row and _dominates(other, row) for other in remaining)
        ]
        if not front:
            raise RuntimeError("typed-route Pareto ranking found no nondominated front")
        front.sort(key=lambda r: (str(r.get("target_qid", "")), str(r.get("route_family", "")), str(r.get("action_id", ""))))
        ids = {id(row) for row in front}
        for row in front:
            row["pareto_front_rank"] = front_rank
            row["pareto_dimensions_scalarized"] = False
            row["frontier_rank_is_truth_rank"] = False
            ranked.append(row)
        remaining = [row for row in remaining if id(row) not in ids]
        front_rank += 1
    return ranked


def select_route_actions(actions: list[dict[str, Any]], *, max_targets: int) -> list[dict[str, Any]]:
    if max_targets < 0:
        raise ValueError("max_targets must be non-negative")
    selected: list[dict[str, Any]] = []
    targets: set[str] = set()
    for row in pareto_rank_actions(actions):
        target = str(row.get("target_qid", "")).strip()
        if not target or target in targets:
            continue
        selected.append(row)
        targets.add(target)
        if len(selected) >= max_targets:
            break
    return selected


def seed_rows(selected: list[dict[str, Any]], *, iteration_index: int) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for index, action in enumerate(selected, start=1):
        rows.append({
            "seed_id": f"world-research-route-{iteration_index}-{index}",
            "seed_state": "budgeted-typed-route",
            "qid": str(action.get("target_qid", "")),
            "coordinate_role": "semantic-gap-typed-route-acquisition",
            "identity_scope": "explicit-route-target-qid",
            "route_action_id": str(action.get("action_id", "")),
            "route_family": str(action.get("route_family", "")),
            "route_source_qid": str(action.get("source_qid", "")),
            "route_property_id": str(action.get("property_id", "")),
            "route_direction": str(action.get("route_direction", "")),
            "pareto_front_rank": int(action.get("pareto_front_rank", 0) or 0),
            "route_creates_claim_truth": False,
            "candidate_only": True,
            "semantic_promotion": False,
        })
    return rows


def update_yield_history(existing: dict[str, Any] | None, plan: dict[str, Any], gap_flow: dict[str, Any], delta_graph: dict[str, Any]) -> dict[str, Any]:
    history = dict(existing or {})
    families = {str(k): dict(v) for k, v in ((history.get("route_families") or {}).items()) if isinstance(v, dict)}
    selected = [row for row in plan.get("selected_route_actions") or [] if isinstance(row, dict)]
    selected_families = sorted({str(row.get("route_family", "")) for row in selected if row.get("route_family")})
    network_requests = int(((delta_graph.get("transport") or {}).get("network_requests", 0)) or 0)
    atoms_by_qid = gap_flow.get("atoms_added_per_selected_qid") or {}
    for family in selected_families:
        row = families.setdefault(family, {
            "observed_rounds": 0,
            "trusted_single_family_rounds": 0,
            "contracted_old_gaps": 0,
            "retired_obligations": 0,
            "new_gap_atoms": 0,
            "network_requests": 0,
            "atoms_added": 0,
            "causal_attribution_paid": False,
        })
        row["observed_rounds"] = int(row.get("observed_rounds", 0)) + 1
        row["atoms_added"] = int(row.get("atoms_added", 0)) + sum(
            int(atoms_by_qid.get(str(a.get("target_qid", "")), 0) or 0)
            for a in selected if str(a.get("route_family", "")) == family
        )
        if len(selected_families) == 1:
            row["trusted_single_family_rounds"] = int(row.get("trusted_single_family_rounds", 0)) + 1
            row["contracted_old_gaps"] = int(row.get("contracted_old_gaps", 0)) + int(gap_flow.get("contracted_gap_atoms", 0) or 0)
            row["retired_obligations"] = int(row.get("retired_obligations", 0)) + int(gap_flow.get("retired_obligations", 0) or 0)
            row["new_gap_atoms"] = int(row.get("new_gap_atoms", 0)) + int(gap_flow.get("new_gap_atoms", 0) or 0)
            row["network_requests"] = int(row.get("network_requests", 0)) + network_requests
        row["causal_attribution_paid"] = False
    return {
        "schema": HISTORY_SCHEMA,
        "route_families": families,
        "mixed_family_rounds_do_not_pay_causal_yield": True,
        "route_yield_creates_truth": False,
        "candidate_only": True,
        "semantic_promotion": False,
    }


def self_check() -> int:
    graph = {
        "schema": "slr-wikimedia-world-follow-v1",
        "item_property_edges": [{"source": "Q1", "property_id": "P279", "target": "Q2", "edge_class": "parent"}],
        "first_link_candidates": [{"from_qid": "Q1", "candidate_qid": "Q3", "ibrahim_parser_equivalence_paid": False, "historical_snapshot_identity_paid": False}],
    }
    closure = {
        "schema": "slr-semantic-world-closure-v1",
        "canonical_atoms": [
            {"kind": "wiki-link", "subject_qid": "Q1", "object_qid": "Q2"},
            {"kind": "wiki-link", "subject_qid": "Q1", "object_qid": "Q3"},
        ],
        "acquisition_obligations": [
            {"obligation_kind": "follow-related-qid", "qid": "Q2", "cross_language_gap_coverage": 4, "source_surface_support": 2, "root_qid_support": 1, "candidate_only": True},
            {"obligation_kind": "follow-related-qid", "qid": "Q3", "cross_language_gap_coverage": 2, "source_surface_support": 1, "root_qid_support": 1, "candidate_only": True},
        ],
    }
    actions = build_route_actions(closure, graph, None)
    assert any(a["route_family"] == "wikidata-subclass-parent" and a["property_id"] == "P279" for a in actions)
    first = next(a for a in actions if a["route_family"] == "wikipedia-first-link")
    assert first["ibrahim_parser_equivalence_paid"] is False
    selected = select_route_actions(actions, max_targets=2)
    assert selected and all(a["pareto_dimensions_scalarized"] is False for a in selected)
    print(
        "SLR_WORLD_RESEARCH_ROUTE_PARETO_SELF_CHECK schema=slr-world-research-route-pareto-v1 passed=true "
        "typed_qp_routes=true ibrahim_historical_equivalence=false pareto_dimensions_scalarized=false "
        "route_creates_claim_truth=false semantic_promotion=false",
        file=sys.stderr,
    )
    return 0


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser()
    sub = p.add_subparsers(dest="command", required=True)
    plan = sub.add_parser("plan")
    plan.add_argument("--closure", type=Path, required=True)
    plan.add_argument("--graph", type=Path, required=True)
    plan.add_argument("--output", type=Path, required=True)
    plan.add_argument("--seeds", type=Path, required=True)
    plan.add_argument("--history", type=Path)
    plan.add_argument("--iteration-index", type=int, default=1)
    plan.add_argument("--max-targets", type=int, default=4)
    update = sub.add_parser("update-history")
    update.add_argument("--plan", type=Path, required=True)
    update.add_argument("--gap-flow", type=Path, required=True)
    update.add_argument("--delta-graph", type=Path, required=True)
    update.add_argument("--history", type=Path)
    update.add_argument("--output", type=Path, required=True)
    sub.add_parser("self-check")
    return p.parse_args()


def main() -> int:
    args = parse_args()
    if args.command == "self-check":
        return self_check()
    if args.command == "plan":
        closure = load(args.closure)
        graph = load(args.graph)
        history = load(args.history) if args.history and args.history.exists() else None
        actions = build_route_actions(closure, graph, history)
        ranked = pareto_rank_actions(actions)
        selected = select_route_actions(actions, max_targets=args.max_targets)
        payload = {
            "schema": SCHEMA,
            "iteration_index": args.iteration_index,
            "route_candidates": ranked,
            "selected_route_actions": selected,
            "pareto_axes": [{"field": field, "direction": direction} for field, direction in PARETO_AXES],
            "pareto_dimensions_scalarized": False,
            "frontier_rank_is_truth_rank": False,
            "typed_property_is_claim_truth": False,
            "current_first_link_is_historical_ibrahim_edge": False,
            "sensiblaw_control_plane_only": True,
            "candidate_only": True,
            "semantic_promotion": False,
            "summary": {
                "route_candidates": len(ranked),
                "selected_route_actions": len(selected),
                "selected_targets": len({str(a.get('target_qid', '')) for a in selected}),
                "pareto_fronts": 1 + max((int(a.get("pareto_front_rank", 0)) for a in ranked), default=-1),
            },
        }
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        seeds = seed_rows(selected, iteration_index=args.iteration_index)
        args.seeds.parent.mkdir(parents=True, exist_ok=True)
        args.seeds.write_text("".join(json.dumps(row, sort_keys=True) + "\n" for row in seeds), encoding="utf-8")
        print(
            "SLR_WORLD_RESEARCH_ROUTE_PARETO_RECEIPT "
            f"schema={SCHEMA} route_candidates={len(ranked)} selected_route_actions={len(selected)} "
            f"selected_targets={payload['summary']['selected_targets']} pareto_fronts={payload['summary']['pareto_fronts']} "
            "pareto_dimensions_scalarized=false frontier_rank_is_truth_rank=false typed_property_is_claim_truth=false "
            "ibrahim_historical_equivalence=false sensiblaw_control_plane_only=true candidate_only=true semantic_promotion=false",
            file=sys.stderr,
        )
        return 0
    if args.command == "update-history":
        existing = load(args.history) if args.history and args.history.exists() else None
        history = update_yield_history(existing, load(args.plan), load(args.gap_flow), load(args.delta_graph))
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(history, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        print(
            "SLR_WORLD_RESEARCH_ROUTE_YIELD_HISTORY_RECEIPT "
            f"schema={HISTORY_SCHEMA} route_families={len(history['route_families'])} "
            "mixed_family_rounds_do_not_pay_causal_yield=true route_yield_creates_truth=false candidate_only=true semantic_promotion=false",
            file=sys.stderr,
        )
        return 0
    raise SystemExit("unknown command")


if __name__ == "__main__":
    raise SystemExit(main())
