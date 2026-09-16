#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

SCHEMA = "slr-world-research-gap-flow-v1"


def load(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise SystemExit(f"expected JSON object: {path}")
    return value


def gap_atom_keys(closure: dict[str, Any]) -> set[str]:
    keys: set[str] = set()
    for gap in closure.get("gaps") or []:
        if not isinstance(gap, dict):
            continue
        sid = str(gap.get("surface_id", ""))
        for atom_id in gap.get("missing_atom_ids") or []:
            if sid and atom_id:
                keys.add(f"{sid}|{atom_id}")
    return keys


def obligation_key(row: dict[str, Any]) -> str:
    kind = str(row.get("obligation_kind", ""))
    qid = str(row.get("qid", ""))
    if kind == "missing-language-surface":
        return f"{kind}|{qid}|{str(row.get('language', ''))}"
    return f"{kind}|{qid}"


def obligation_keys(closure: dict[str, Any]) -> set[str]:
    return {
        obligation_key(row)
        for row in closure.get("acquisition_obligations") or []
        if isinstance(row, dict) and obligation_key(row) not in {"|", "follow-related-qid|", "missing-language-surface||"}
    }


def atom_root(atom: dict[str, Any]) -> str:
    if str(atom.get("kind", "")) == "qid":
        return str(atom.get("qid", ""))
    return str(atom.get("subject_qid", ""))


def compare_closures(previous: dict[str, Any], current: dict[str, Any], *, selected_qids: list[str]) -> dict[str, Any]:
    if previous.get("schema") != "slr-semantic-world-closure-v1" or current.get("schema") != "slr-semantic-world-closure-v1":
        raise ValueError("semantic closure schema mismatch")

    prior_gaps = gap_atom_keys(previous)
    current_gaps = gap_atom_keys(current)
    contracted = prior_gaps - current_gaps
    persisting = prior_gaps & current_gaps
    opened = current_gaps - prior_gaps

    prior_obligations = obligation_keys(previous)
    current_obligations = obligation_keys(current)

    previous_atoms = {
        str(atom.get("atom_id", ""))
        for atom in previous.get("canonical_atoms") or []
        if isinstance(atom, dict) and atom.get("atom_id")
    }
    added_by_qid: dict[str, int] = {qid: 0 for qid in selected_qids}
    selected = set(selected_qids)
    for atom in current.get("canonical_atoms") or []:
        if not isinstance(atom, dict):
            continue
        aid = str(atom.get("atom_id", ""))
        if not aid or aid in previous_atoms:
            continue
        root = atom_root(atom)
        if root in selected:
            added_by_qid[root] += 1

    return {
        "schema": SCHEMA,
        "prior_gap_atoms": len(prior_gaps),
        "current_gap_atoms": len(current_gaps),
        "contracted_gap_atoms": len(contracted),
        "persisting_gap_atoms": len(persisting),
        "new_gap_atoms": len(opened),
        "net_gap_delta": len(current_gaps) - len(prior_gaps),
        "prior_obligations": len(prior_obligations),
        "current_obligations": len(current_obligations),
        "retired_obligations": len(prior_obligations - current_obligations),
        "persisting_obligations": len(prior_obligations & current_obligations),
        "new_obligations": len(current_obligations - prior_obligations),
        "atoms_added_per_selected_qid": added_by_qid,
        "net_gap_growth_implies_no_contraction": False,
        "gap_contraction_creates_claim_truth": False,
        "candidate_only": True,
        "semantic_promotion": False,
    }


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser()
    p.add_argument("--previous", type=Path)
    p.add_argument("--current", type=Path)
    p.add_argument("--plan", type=Path)
    p.add_argument("--output", type=Path)
    p.add_argument("--self-check", action="store_true")
    return p.parse_args()


def self_check() -> int:
    previous = {
        "schema": "slr-semantic-world-closure-v1",
        "canonical_atoms": [],
        "gaps": [{"surface_id": "Q1:en", "missing_atom_ids": ["a", "b"]}],
        "acquisition_obligations": [{"obligation_kind": "follow-related-qid", "qid": "Q2"}],
    }
    current = {
        "schema": "slr-semantic-world-closure-v1",
        "canonical_atoms": [],
        "gaps": [{"surface_id": "Q1:en", "missing_atom_ids": ["b", "c", "d"]}],
        "acquisition_obligations": [{"obligation_kind": "follow-related-qid", "qid": "Q3"}],
    }
    flow = compare_closures(previous, current, selected_qids=[])
    assert flow["contracted_gap_atoms"] == 1
    assert flow["new_gap_atoms"] == 2
    assert flow["net_gap_delta"] == 1
    assert flow["net_gap_growth_implies_no_contraction"] is False
    print(
        "SLR_WORLD_RESEARCH_GAP_FLOW_SELF_CHECK schema=slr-world-research-gap-flow-v1 passed=true "
        "net_gap_growth_implies_no_contraction=false gap_contraction_creates_claim_truth=false semantic_promotion=false",
        file=sys.stderr,
    )
    return 0


def main() -> int:
    args = parse_args()
    if args.self_check:
        return self_check()
    if not all([args.previous, args.current, args.plan, args.output]):
        raise SystemExit("--previous, --current, --plan and --output are required unless --self-check")
    previous = load(args.previous)
    current = load(args.current)
    plan = load(args.plan)
    selected_qids = [str(row.get("qid", "")) for row in plan.get("selected_related_qids") or [] if isinstance(row, dict) and row.get("qid")]
    flow = compare_closures(previous, current, selected_qids=selected_qids)
    flow["previous_closure_reference"] = str(args.previous)
    flow["current_closure_reference"] = str(args.current)
    flow["budget_plan_reference"] = str(args.plan)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(flow, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(
        "SLR_WORLD_RESEARCH_GAP_FLOW_RECEIPT "
        f"schema={SCHEMA} prior_gap_atoms={flow['prior_gap_atoms']} contracted_gap_atoms={flow['contracted_gap_atoms']} "
        f"persisting_gap_atoms={flow['persisting_gap_atoms']} new_gap_atoms={flow['new_gap_atoms']} net_gap_delta={flow['net_gap_delta']} "
        f"prior_obligations={flow['prior_obligations']} retired_obligations={flow['retired_obligations']} "
        f"persisting_obligations={flow['persisting_obligations']} new_obligations={flow['new_obligations']} "
        "net_gap_growth_implies_no_contraction=false gap_contraction_creates_claim_truth=false candidate_only=true semantic_promotion=false",
        file=sys.stderr,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
