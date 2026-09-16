#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import sys
from copy import deepcopy
from pathlib import Path
from typing import Any

SCHEMA = "slr-claim-fragment-projection-v1"
TARGET_SCHEMA = "sl.candidate_world_model.v0_1"


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser()
    p.add_argument("--world", type=Path, required=True)
    p.add_argument("--paths", type=Path, required=True)
    p.add_argument("--source", type=Path, required=True)
    p.add_argument("--output", type=Path, required=True)
    return p.parse_args()


def fragment_state(segment: dict[str, Any], side: str) -> str:
    state = str(segment.get(f"boundary_{side}_state", ""))
    if state == "exact":
        return "exact-boundary"
    if state == "bounded":
        return "bounded-boundary"
    if state in {"sentence-start", "sentence-end"}:
        return "context-boundary"
    return "unpaid-boundary"


def main() -> int:
    args = parse_args()
    world = json.loads(args.world.read_text(encoding="utf-8"))
    paths = json.loads(args.paths.read_text(encoding="utf-8"))
    source = args.source.read_text(encoding="utf-8")

    if world.get("schema_version") != TARGET_SCHEMA:
        raise SystemExit("unexpected CandidateWorldModel schema")
    if paths.get("schema") != "slr-labelled-discourse-path-v1":
        raise SystemExit("unexpected discourse-path schema")
    if bool((world.get("metadata") or {}).get("semantic_promotion", False)):
        raise SystemExit("refusing semantically promoted world model")

    out = deepcopy(world)
    claims = list(out.get("claims") or [])
    relations = list(out.get("relations") or [])
    existing_nodes = {str(n.get("node_id", "")) for n in claims if isinstance(n, dict)}
    existing_relations = {str(r.get("relation_id", "")) for r in relations if isinstance(r, dict)}

    fragments = 0
    claim_fragments = 0
    intermediate_fragments = 0
    exact_boundary_fragments = 0
    bounded_boundary_fragments = 0

    for path in paths.get("paths", []):
        if not isinstance(path, dict):
            continue
        sentence = path.get("parser_sentence")
        segments = [s for s in path.get("segments", []) if isinstance(s, dict)]
        last_index = len(segments) - 1
        for segment in segments:
            idx = int(segment.get("segment_index", 0))
            start = int(segment.get("char_start", 0))
            end = int(segment.get("char_end", 0))
            if not (0 <= start < end <= len(source)):
                raise SystemExit(f"invalid fragment offsets sentence={sentence} segment={idx}")

            claim_ref = ""
            role = "intermediate-discourse-fragment"
            if idx == 0:
                claim_ref = str(path.get("left_claim", ""))
                role = "left-claim-local-fragment"
            elif idx == last_index:
                claim_ref = str(path.get("right_claim", ""))
                role = "right-claim-local-fragment"

            fragment_id = f"claim-fragment:s{sentence}:{idx}:{start}-{end}"
            left_state = fragment_state(segment, "before")
            right_state = fragment_state(segment, "after")
            boundary_states = {left_state, right_state}
            if "exact-boundary" in boundary_states:
                exact_boundary_fragments += 1
            if "bounded-boundary" in boundary_states:
                bounded_boundary_fragments += 1

            node = {
                "node_id": fragment_id,
                "node_kind": "canonical_claim_local_fragment" if claim_ref else "intermediate_discourse_fragment",
                "label": f"sentence {sentence} segment {idx}: {segment.get('speaker', '')}",
                "status": "candidate",
                "source_anchor_ids": [f"sentence:{sentence}"],
                "conflict_ids": [],
                "promotion_status": "candidate_only",
                "residual": {
                    "left_boundary_payment": left_state,
                    "right_boundary_payment": right_state,
                    "whole_claim_extent_paid": False,
                    "claim_truth_promoted": False,
                },
                "metadata": {
                    "schema": SCHEMA,
                    "parser_sentence": sentence,
                    "segment_index": idx,
                    "speaker": segment.get("speaker", ""),
                    "char_start": start,
                    "char_end": end,
                    "text": source[start:end],
                    "claim_ref": claim_ref,
                    "fragment_role": role,
                    "path_state": path.get("path_state", ""),
                    "direct_handoff": bool(path.get("direct_handoff", False)),
                    "semantic_promotion": False,
                    "candidate_only": True,
                },
            }
            if fragment_id not in existing_nodes:
                claims.append(node)
                existing_nodes.add(fragment_id)
                fragments += 1
                if claim_ref:
                    claim_fragments += 1
                else:
                    intermediate_fragments += 1

            if claim_ref:
                target = f"canonical-claim:{claim_ref}"
                relation_id = f"claim-fragment-projection:{fragment_id}:{claim_ref}"
                if relation_id not in existing_relations:
                    relations.append({
                        "relation_id": relation_id,
                        "source_id": fragment_id,
                        "target_id": target,
                        "relation_kind": "candidate_local_fragment_of_canonical_claim",
                        "status": "candidate",
                        "source_anchor_ids": [f"sentence:{sentence}"],
                        "promotion_status": "candidate_only",
                        "residual": {
                            "whole_claim_extent_paid": False,
                            "left_boundary_payment": left_state,
                            "right_boundary_payment": right_state,
                        },
                        "metadata": {
                            "schema": SCHEMA,
                            "claim_ref": claim_ref,
                            "semantic_promotion": False,
                            "claim_truth_promoted": False,
                        },
                    })
                    existing_relations.add(relation_id)

    out["claims"] = claims
    out["relations"] = relations
    metadata = dict(out.get("metadata") or {})
    metadata["claim_fragment_projection"] = {
        "schema": SCHEMA,
        "source_path_schema": paths.get("schema"),
        "whole_claim_extent_paid": False,
        "intermediate_speaker_segments_retained": True,
        "skip_intermediate_speaker_forbidden": True,
        "candidate_only": True,
        "semantic_promotion": False,
        "claim_truth_promoted": False,
    }
    out["metadata"] = metadata
    summary = dict(out.get("summary") or {})
    summary.update({
        "claim_fragment_node_count": claim_fragments,
        "intermediate_discourse_fragment_count": intermediate_fragments,
        "claim_fragment_projection_edge_count": claim_fragments,
        "exact_boundary_fragment_count": exact_boundary_fragments,
        "bounded_boundary_fragment_count": bounded_boundary_fragments,
    })
    out["summary"] = summary

    status_counts = {"candidate": 0, "conflicted": 0}
    for collection in (claims, relations):
        for item in collection:
            if not isinstance(item, dict):
                continue
            status = str(item.get("status", ""))
            if status in status_counts:
                status_counts[status] += 1
    out["status_counts"] = status_counts

    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(out, indent=2, ensure_ascii=False, sort_keys=True) + "\n", encoding="utf-8")
    print(
        "SLR_CLAIM_FRAGMENT_PROJECTION_RECEIPT "
        f"schema={SCHEMA} fragments={fragments} claim_fragments={claim_fragments} "
        f"intermediate_fragments={intermediate_fragments} exact_boundary_fragments={exact_boundary_fragments} "
        f"bounded_boundary_fragments={bounded_boundary_fragments} whole_claim_extent_paid=false "
        "intermediate_speaker_segments_retained=true candidate_only=true semantic_promotion=false claim_truth_promoted=false",
        file=sys.stderr,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
