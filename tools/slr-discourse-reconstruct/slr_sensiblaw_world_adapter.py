#!/usr/bin/env python3
from __future__ import annotations

import argparse
import csv
import json
import sys
from pathlib import Path
from typing import Any, Iterable

SCHEMA = "slr-sensiblaw-world-adapter-v1"
TARGET_SCHEMA = "sl.candidate_world_model.v0_1"


def rows(path: Path) -> list[dict[str, str]]:
    with path.open("r", encoding="utf-8", newline="") as handle:
        return list(csv.DictReader(handle, delimiter="\t"))


def truth(value: str | None) -> bool:
    return str(value or "").strip().lower() in {"1", "true", "yes"}


def integer(value: str | None) -> int:
    try:
        return int(str(value or "0").strip())
    except ValueError:
        return 0


def strings(value: str | None) -> list[str]:
    return [item for item in str(value or "").split(",") if item]


def source_anchors(source_ref: str, *extra: str) -> list[str]:
    return [value for value in (source_ref, *extra) if value]


def build_span_nodes(span_rows: Iterable[dict[str, str]], source_ref: str) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    claims: list[dict[str, Any]] = []
    relations: list[dict[str, Any]] = []
    previous_by_sentence: dict[str, str] = {}

    sorted_rows = sorted(
        span_rows,
        key=lambda row: (integer(row.get("sentence")), integer(row.get("segment_index"))),
    )
    for row in sorted_rows:
        span_id = row.get("span_id", "").strip()
        sentence = row.get("sentence", "").strip()
        if not span_id:
            continue
        segment_index = integer(row.get("segment_index"))
        claims.append(
            {
                "node_id": span_id,
                "node_kind": "discourse_span_candidate",
                "label": f"sentence {sentence} segment {segment_index}",
                "status": "candidate",
                "source_anchor_ids": source_anchors(source_ref, f"sentence:{sentence}"),
                "conflict_ids": [],
                "promotion_status": "candidate_only",
                "residual": {
                    "pareto_fibres": strings(row.get("pareto_fibres")),
                    "residual_fibres": strings(row.get("residual_fibres")),
                    "crossing_roles": strings(row.get("crossing_roles")),
                },
                "metadata": {
                    "schema": row.get("schema", ""),
                    "sentence": integer(sentence),
                    "segment_index": segment_index,
                    "char_start": integer(row.get("char_start")),
                    "char_end": integer(row.get("char_end")),
                    "boundary_before": row.get("boundary_before", ""),
                    "boundary_projection": row.get("boundary_projection", ""),
                    "actor_crossing": truth(row.get("actor_crossing")),
                    "patient_crossing": truth(row.get("patient_crossing")),
                    "clause_crossing": truth(row.get("clause_crossing")),
                    "coordination_crossing": truth(row.get("coordination_crossing")),
                    "predicate_aux_crossing": truth(row.get("predicate_aux_crossing")),
                    "candidate_only": truth(row.get("candidate_only")),
                },
            }
        )
        previous = previous_by_sentence.get(sentence)
        if previous is not None:
            projection = row.get("boundary_projection", "") or "unresolved"
            relations.append(
                {
                    "relation_id": f"adjacency:{previous}:{span_id}",
                    "source_id": previous,
                    "target_id": span_id,
                    "relation_kind": f"discourse_boundary:{projection}",
                    "status": "candidate",
                    "source_anchor_ids": source_anchors(source_ref, f"sentence:{sentence}"),
                    "promotion_status": "candidate_only",
                    "residual": {
                        "pareto_fibres": strings(row.get("pareto_fibres")),
                        "residual_fibres": strings(row.get("residual_fibres")),
                    },
                    "metadata": {
                        "boundary_before": row.get("boundary_before", ""),
                        "crossing_roles": strings(row.get("crossing_roles")),
                        "actor_crossing": truth(row.get("actor_crossing")),
                        "patient_crossing": truth(row.get("patient_crossing")),
                        "clause_crossing": truth(row.get("clause_crossing")),
                        "coordination_crossing": truth(row.get("coordination_crossing")),
                        "predicate_aux_crossing": truth(row.get("predicate_aux_crossing")),
                    },
                }
            )
        previous_by_sentence[sentence] = span_id
    return claims, relations


def build_boundary_nodes(
    quality_rows: Iterable[dict[str, str]],
    role_rows: Iterable[dict[str, str]],
    source_ref: str,
) -> tuple[list[dict[str, Any]], list[dict[str, Any]], list[dict[str, Any]]]:
    role_map = {
        (row.get("sentence", ""), row.get("split", "")): row for row in role_rows
    }
    claims: list[dict[str, Any]] = []
    conflicts: list[dict[str, Any]] = []
    residuals: list[dict[str, Any]] = []

    for row in quality_rows:
        node_id = row.get("node_id", "").strip()
        sentence = row.get("sentence", "").strip()
        split = row.get("split", "").strip()
        if not node_id:
            continue
        role = role_map.get((sentence, split), {})
        projection = row.get("projection", "") or "unresolved"
        unresolved = projection == "unresolved"
        conflict_id = f"conflict:{node_id}" if unresolved else ""
        risk_flags = {
            "attribution_ambiguity": truth(row.get("attribution_ambiguity")),
            "speaker_ambiguity": truth(row.get("speaker_ambiguity")),
            "clause_attribution_ambiguity": truth(row.get("clause_attribution_ambiguity")),
            "hidden_speaker_splice_risk": truth(row.get("hidden_speaker_splice_risk")),
            "false_cut_risk": truth(row.get("false_cut_risk")),
            "negation_side_shift": truth(row.get("negation_side_shift")),
            "modality_side_shift": truth(row.get("modality_side_shift")),
        }
        claims.append(
            {
                "node_id": node_id,
                "node_kind": "discourse_boundary_candidate",
                "label": row.get("anchor", ""),
                "status": "conflicted" if unresolved else "candidate",
                "source_anchor_ids": source_anchors(source_ref, f"sentence:{sentence}"),
                "conflict_ids": [conflict_id] if conflict_id else [],
                "promotion_status": "candidate_only",
                "residual": {
                    "pareto_fibres": strings(row.get("pareto_fibres")),
                    "pareto_width": integer(row.get("pareto_width")),
                    "pnf_residual_count": integer(row.get("pnf_residual_count")),
                    **risk_flags,
                },
                "metadata": {
                    "quality_schema": row.get("schema", ""),
                    "role_schema": role.get("schema", ""),
                    "sentence": integer(sentence),
                    "split": integer(split),
                    "projection": projection,
                    "hard_cut_admissible": truth(row.get("hard_cut_admissible")),
                    "crossing_roles": strings(row.get("crossing_roles")),
                    "actor_crossing": truth(role.get("actor_crossing")),
                    "patient_crossing": truth(role.get("patient_crossing")),
                    "clause_crossing": truth(role.get("clause_crossing")),
                    "coordination_crossing": truth(role.get("coordination_crossing")),
                    "predicate_aux_crossing": truth(role.get("predicate_aux_crossing")),
                    "left_has_subject": truth(role.get("left_has_subject")),
                    "right_has_subject": truth(role.get("right_has_subject")),
                    "left_has_modal": truth(role.get("left_has_modal")),
                    "right_has_modal": truth(role.get("right_has_modal")),
                    "left_has_negation": truth(role.get("left_has_negation")),
                    "right_has_negation": truth(role.get("right_has_negation")),
                    "world_mismatch_observed": row.get("world_mismatch_observed", "not-observed"),
                    "candidate_only": truth(row.get("candidate_only")),
                },
            }
        )
        if unresolved:
            conflicts.append(
                {
                    "conflict_id": conflict_id,
                    "conflict_kind": "discourse_pareto_multiplicity",
                    "candidate_ids": [node_id],
                    "alternatives": strings(row.get("pareto_fibres")),
                    "status": "candidate",
                    "source_anchor_ids": source_anchors(source_ref, f"sentence:{sentence}"),
                }
            )
        if any(risk_flags.values()) or integer(row.get("pnf_residual_count")) > 0:
            residuals.append(
                {
                    "residual_id": f"residual:{node_id}",
                    "candidate_id": node_id,
                    "status": "candidate",
                    "pareto_fibres": strings(row.get("pareto_fibres")),
                    "crossing_roles": strings(row.get("crossing_roles")),
                    "risk_flags": risk_flags,
                    "pnf_residual_count": integer(row.get("pnf_residual_count")),
                    "source_anchor_ids": source_anchors(source_ref, f"sentence:{sentence}"),
                }
            )
    return claims, conflicts, residuals


def provenance_rows(source_ref: str, span_claims: list[dict[str, Any]], boundary_claims: list[dict[str, Any]]) -> list[dict[str, Any]]:
    if not source_ref:
        return []
    return [
        {
            "provenance_id": f"provenance:{claim['node_id']}",
            "source_id": source_ref,
            "target_id": claim["node_id"],
            "relation_kind": "derived_from",
            "status": "candidate",
        }
        for claim in (*span_claims, *boundary_claims)
    ]


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--spans", type=Path, required=True)
    parser.add_argument("--quality", type=Path, required=True)
    parser.add_argument("--roles", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--model-id", required=True)
    parser.add_argument("--source-ref", default="")
    parser.add_argument("--source-sha256", default="")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    for path in (args.spans, args.quality, args.roles):
        if not path.is_file():
            raise SystemExit(f"missing input: {path}")

    span_claims, relations = build_span_nodes(rows(args.spans), args.source_ref)
    boundary_claims, conflicts, residuals = build_boundary_nodes(
        rows(args.quality), rows(args.roles), args.source_ref
    )
    claims = span_claims + boundary_claims
    model = {
        "schema_version": TARGET_SCHEMA,
        "model_id": args.model_id,
        "lane_family": "slr_discourse",
        "model_status": "candidate",
        "source_mode": "slr_tsv_bundle",
        "entities": [],
        "claims": claims,
        "relations": relations,
        "events": [],
        "timelines": [],
        "authority_surfaces": [],
        "provenance_graph": provenance_rows(args.source_ref, span_claims, boundary_claims),
        "conflicts": conflicts,
        "residuals": residuals,
        "update_rules": [],
        "projections": [],
        "external_graph_views": [],
        "external_bridge_candidates": [],
        "external_bridge_decisions": [],
        "external_pressure_results": [],
        "summary": {
            "span_candidate_count": len(span_claims),
            "boundary_candidate_count": len(boundary_claims),
            "relation_count": len(relations),
            "conflict_count": len(conflicts),
            "residual_count": len(residuals),
        },
        "metadata": {
            "adapter_schema": SCHEMA,
            "target_schema": TARGET_SCHEMA,
            "source_ref": args.source_ref,
            "source_sha256": args.source_sha256,
            "input_tables": {
                "spans": str(args.spans),
                "quality": str(args.quality),
                "roles": str(args.roles),
            },
            "world_constraint_status": "not_attached",
            "semantic_promotion": False,
            "candidate_only": True,
        },
        "status_counts": {
            "candidate": sum(1 for claim in claims if claim["status"] == "candidate"),
            "conflicted": sum(1 for claim in claims if claim["status"] == "conflicted"),
        },
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(model, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(
        "SLR_SENSIBLAW_WORLD_ADAPTER_RECEIPT "
        f"schema={SCHEMA} target={TARGET_SCHEMA} model_id={args.model_id} "
        f"claims={len(claims)} relations={len(relations)} conflicts={len(conflicts)} "
        f"residuals={len(residuals)} world_constraints_attached=false "
        "candidate_only=true semantic_promotion=false",
        file=sys.stderr,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
