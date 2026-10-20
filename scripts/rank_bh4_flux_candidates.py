#!/usr/bin/env python3
"""Rank BH4 kinetic candidates for flux-bound adjudication without auto-payment.

Input is the executed SABIO->Rhea adjudication worklist. The output groups
candidates by finite Rhea column and ranks them by *flux relevance* only. It
never converts assay kinetics into solver bounds. Every candidate carries four
explicit payment gates; `usable_for_flux_bound` is true only if all four gates
are already true in an upstream/manual adjudication record.
"""

from __future__ import annotations

import argparse
import json
from collections import defaultdict
from pathlib import Path
from typing import Any

KIND_PRIORITY = {
    "rate-like": 50,
    "catalytic-constant-like": 40,
    "affinity-like": 20,
    "inhibitory-like": 15,
    "concentration-like": 5,
    "unclassified": 0,
}


def _has_numeric(value: Any) -> bool:
    if value is None or value == "":
        return False
    try:
        float(value)
        return True
    except (TypeError, ValueError):
        return False


def relevance_class(kind: str) -> str:
    if kind == "rate-like":
        return "direct-rate-candidate"
    if kind == "catalytic-constant-like":
        return "capacity-candidate"
    if kind in {"affinity-like", "inhibitory-like"}:
        return "kinetic-shape-candidate"
    if kind == "concentration-like":
        return "assay-context-only"
    return "not-flux-informative"


def candidate_score(row: dict) -> int:
    kind = str(row.get("parameter_kind_hint") or "unclassified")
    score = KIND_PRIORITY.get(kind, 0)
    if _has_numeric(row.get("n_start_value")):
        score += 4
    if _has_numeric(row.get("n_end_value")):
        score += 2
    if row.get("unit"):
        score += 3
    if row.get("entry_id"):
        score += 1
    if row.get("parameter_name") or row.get("parameter_type") or row.get("sbo_term"):
        score += 1
    return score


def payment_gates(row: dict) -> dict[str, bool]:
    # Upstream/manual adjudication may eventually provide these booleans.
    # Default is fail-closed: absent coordinates are unpaid, never inferred.
    return {
        "assay_reaction_identity_paid": bool(row.get("assay_reaction_identity_paid", False)),
        "same_object_compartment_time_paid": bool(row.get("same_object_compartment_time_paid", False)),
        "normalized_solver_flux_unit_paid": bool(row.get("normalized_solver_flux_unit_paid", False)),
        "kinetic_to_flux_translation_paid": bool(row.get("kinetic_to_flux_translation_paid", False)),
    }


def rank(adjudication: dict, matrix: dict, top_n: int) -> dict:
    finite_reactions = [str(x) for x in matrix.get("reaction_index", [])]
    grouped: dict[str, list[dict]] = defaultdict(list)

    for row in adjudication.get("rows", []):
        for rid in row.get("finite_matrix_rhea_ids", []):
            gates = payment_gates(row)
            ranked = {
                "rhea_id": rid,
                "symbol": row.get("symbol"),
                "accession": row.get("accession"),
                "entry_id": row.get("entry_id"),
                "parameter_name": row.get("parameter_name"),
                "parameter_type": row.get("parameter_type"),
                "sbo_term": row.get("sbo_term"),
                "parameter_kind_hint": row.get("parameter_kind_hint", "unclassified"),
                "flux_relevance_class": relevance_class(str(row.get("parameter_kind_hint") or "unclassified")),
                "n_start_value": row.get("n_start_value"),
                "n_end_value": row.get("n_end_value"),
                "unit": row.get("unit"),
                "candidate_quality_score": candidate_score(row),
                **gates,
            }
            ranked["usable_for_flux_bound"] = all(gates.values())
            ranked["blocked_by"] = [name for name, paid in gates.items() if not paid]
            grouped[rid].append(ranked)

    reaction_ledgers = []
    payable_reactions = []
    blocked_reactions = []
    for rid in finite_reactions:
        candidates = sorted(
            grouped.get(rid, []),
            key=lambda row: (
                -int(row["candidate_quality_score"]),
                str(row.get("entry_id") or ""),
                str(row.get("parameter_name") or ""),
            ),
        )
        top = candidates[:top_n]
        payable = any(row["usable_for_flux_bound"] for row in candidates)
        if payable:
            payable_reactions.append(rid)
        else:
            blocked_reactions.append(rid)
        reaction_ledgers.append({
            "rhea_id": rid,
            "candidate_count": len(candidates),
            "direct_rate_candidate_count": sum(row["flux_relevance_class"] == "direct-rate-candidate" for row in candidates),
            "capacity_candidate_count": sum(row["flux_relevance_class"] == "capacity-candidate" for row in candidates),
            "payable_candidate_count": sum(bool(row["usable_for_flux_bound"]) for row in candidates),
            "reaction_flux_bound_payable": payable,
            "top_candidates": top,
        })

    return {
        "schema": "dashi.bh4-flux-candidate-ranking.v1",
        "source_adjudication_schema": adjudication.get("schema"),
        "source_matrix_schema": matrix.get("schema"),
        "finite_reaction_count": len(finite_reactions),
        "finite_reactions_with_any_candidate": sum(bool(grouped.get(rid)) for rid in finite_reactions),
        "payable_reaction_count": len(payable_reactions),
        "blocked_reaction_count": len(blocked_reactions),
        "payable_reactions": payable_reactions,
        "blocked_reactions": blocked_reactions,
        "top_candidates_by_reaction": reaction_ledgers,
        "promotion_boundary": {
            "candidate_rank_creates_flux_bound": False,
            "rate_like_class_creates_flux_bound": False,
            "catalytic_constant_creates_flux_without_enzyme_abundance": False,
            "assay_context_may_be_dropped": False,
            "missing_payment_gate_defaults_true": False,
        },
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--adjudication", type=Path, required=True)
    parser.add_argument("--matrix", type=Path, required=True)
    parser.add_argument("--top-n", type=int, default=10)
    parser.add_argument("-o", "--output", type=Path)
    args = parser.parse_args()
    if args.top_n < 1:
        raise SystemExit("--top-n must be >= 1")
    result = rank(
        json.loads(args.adjudication.read_text(encoding="utf-8")),
        json.loads(args.matrix.read_text(encoding="utf-8")),
        args.top_n,
    )
    text = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text, encoding="utf-8")
    else:
        print(text, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
