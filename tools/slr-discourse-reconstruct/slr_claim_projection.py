#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import sys
from copy import deepcopy
from pathlib import Path
from typing import Any

SCHEMA = "slr-canonical-claim-projection-v1"
TARGET_SCHEMA = "sl.candidate_world_model.v0_1"


def read_jsonl(path: Path) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for line in path.read_text(encoding="utf-8").splitlines():
        line = line.strip()
        if line:
            rows.append(json.loads(line))
    return rows


def integer(value: Any) -> int | None:
    try:
        return int(value)
    except (TypeError, ValueError):
        return None


def node_sentence(node: dict[str, Any]) -> int | None:
    metadata = node.get("metadata")
    if isinstance(metadata, dict):
        return integer(metadata.get("sentence"))
    return None


def claim_node(claim_ref: str, fixture: dict[str, Any]) -> dict[str, Any]:
    return {
        "node_id": f"canonical-claim:{claim_ref}",
        "node_kind": "canonical_claim_reference",
        "label": claim_ref,
        "status": "candidate",
        "source_anchor_ids": [claim_ref],
        "conflict_ids": [],
        "promotion_status": "reference_only",
        "residual": {
            "exact_span_weld": "unpaid",
            "speaker_status_from_fixture_used_as_authority": False,
        },
        "metadata": {
            "claim_ref": claim_ref,
            "parser_sentence_ids": fixture.get("parser_sentence_ids", []),
            "text_role": fixture.get("text_role", ""),
            "mapping_basis": "repo fixture claim_ref + parser_sentence_ids",
            "fixture_candidate_status_retained_as_historical_metadata": fixture.get("candidate_status", ""),
            "fixture_candidate_speaker_retained_as_historical_metadata": fixture.get("candidate_speaker", ""),
            "current_speaker_payment_source": "separate primary-source attribution owner",
            "semantic_promotion": False,
        },
    }


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser()
    p.add_argument("--world", type=Path, required=True)
    p.add_argument("--fixture", type=Path, required=True)
    p.add_argument("--cuts", type=Path, required=True)
    p.add_argument("--output", type=Path, required=True)
    return p.parse_args()


def main() -> int:
    args = parse_args()
    world = json.loads(args.world.read_text(encoding="utf-8"))
    if world.get("schema_version") != TARGET_SCHEMA:
        raise SystemExit(f"unexpected world schema: {world.get('schema_version')!r}")

    fixtures = read_jsonl(args.fixture)
    cuts = read_jsonl(args.cuts)
    out = deepcopy(world)
    claims = list(out.get("claims") or [])
    relations = list(out.get("relations") or [])
    conflicts = list(out.get("conflicts") or [])
    residuals = list(out.get("residuals") or [])

    existing_ids = {str(node.get("node_id", "")) for node in claims if isinstance(node, dict)}
    relation_ids = {str(edge.get("relation_id", "")) for edge in relations if isinstance(edge, dict)}

    fixture_claims = [row for row in fixtures if row.get("claim_ref")]
    added_claim_refs = 0
    added_projection_edges = 0
    ambiguous_sentence_mappings = 0

    claim_to_sentences: dict[str, list[int]] = {}
    sentence_to_claims: dict[int, set[str]] = {}
    for fixture in fixture_claims:
        claim_ref = str(fixture["claim_ref"])
        sentence_ids = [s for s in (integer(v) for v in fixture.get("parser_sentence_ids", [])) if s is not None]
        claim_to_sentences[claim_ref] = sentence_ids
        for sentence in sentence_ids:
            sentence_to_claims.setdefault(sentence, set()).add(claim_ref)
        canonical_id = f"canonical-claim:{claim_ref}"
        if canonical_id not in existing_ids:
            claims.append(claim_node(claim_ref, fixture))
            existing_ids.add(canonical_id)
            added_claim_refs += 1

    discourse_nodes = [
        node for node in claims
        if isinstance(node, dict)
        and node.get("node_kind") in {"discourse_span_candidate", "discourse_boundary_candidate"}
    ]

    for claim_ref, sentence_ids in claim_to_sentences.items():
        canonical_id = f"canonical-claim:{claim_ref}"
        for node in discourse_nodes:
            sentence = node_sentence(node)
            if sentence is None or sentence not in sentence_ids:
                continue
            source_id = str(node.get("node_id", ""))
            relation_id = f"claim-projection:{source_id}:{claim_ref}"
            if not source_id or relation_id in relation_ids:
                continue
            competing = sorted(sentence_to_claims.get(sentence, set()))
            ambiguous = len(competing) > 1
            relations.append({
                "relation_id": relation_id,
                "source_id": source_id,
                "target_id": canonical_id,
                "relation_kind": "candidate_projection_to_canonical_claim",
                "status": "conflicted" if ambiguous else "candidate",
                "source_anchor_ids": list(node.get("source_anchor_ids") or []),
                "promotion_status": "candidate_only",
                "residual": {
                    "exact_span_weld": "unpaid",
                    "competing_claim_refs_for_sentence": competing,
                    "requires_labelled_alignment_or_exact_cut_receipt": ambiguous,
                },
                "metadata": {
                    "schema": SCHEMA,
                    "parser_sentence_id": sentence,
                    "claim_ref": claim_ref,
                    "mapping_basis": "explicit repo fixture parser_sentence_ids",
                    "speaker_status_imported_from_fixture": False,
                    "semantic_promotion": False,
                },
            })
            relation_ids.add(relation_id)
            added_projection_edges += 1
            if ambiguous:
                ambiguous_sentence_mappings += 1

    cut_constraints: list[dict[str, Any]] = []
    for row in cuts:
        if not (row.get("left_claim") and row.get("right_claim")):
            continue
        constraint = {
            "sentence_ref": row.get("sentence_ref", ""),
            "left_claim": row.get("left_claim", ""),
            "right_claim": row.get("right_claim", ""),
            "cut_anchor": row.get("cut_anchor", ""),
            "historical_status": row.get("status", row.get("left_status", "")),
            "verification_required_in_fixture": bool(row.get("verification_required", False)),
            "role": "claim projection disambiguation constraint",
            "semantic_promotion": False,
        }
        cut_constraints.append(constraint)

    metadata = dict(out.get("metadata") or {})
    metadata["canonical_claim_projection"] = {
        "schema": SCHEMA,
        "fixture": str(args.fixture),
        "cuts": str(args.cuts),
        "claim_identity_mapping_basis": "explicit repo fixture",
        "fixture_speaker_status_is_authority": False,
        "exact_subspan_weld_default": "unpaid",
        "cut_constraints": cut_constraints,
        "semantic_promotion": False,
        "candidate_only": True,
    }
    out["metadata"] = metadata
    out["claims"] = claims
    out["relations"] = relations
    out["conflicts"] = conflicts
    out["residuals"] = residuals

    summary = dict(out.get("summary") or {})
    summary.update({
        "canonical_claim_reference_count": added_claim_refs,
        "candidate_claim_projection_edge_count": added_projection_edges,
        "ambiguous_sentence_projection_edge_count": ambiguous_sentence_mappings,
        "claim_projection_cut_constraint_count": len(cut_constraints),
    })
    out["summary"] = summary

    # Preserve the target ABI while refreshing status counts using SensibLaw's
    # collection semantics: candidate/conflicted claims and relations both count.
    status_counts = {"candidate": 0, "conflicted": 0}
    for collection in (claims, relations):
        for item in collection:
            status = str(item.get("status", "")) if isinstance(item, dict) else ""
            if status in status_counts:
                status_counts[status] += 1
    out["status_counts"] = status_counts

    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(out, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(
        "SLR_CANONICAL_CLAIM_PROJECTION_RECEIPT "
        f"schema={SCHEMA} target={TARGET_SCHEMA} claim_refs={added_claim_refs} "
        f"projection_edges={added_projection_edges} ambiguous_sentence_edges={ambiguous_sentence_mappings} "
        f"cut_constraints={len(cut_constraints)} exact_span_weld_default=unpaid "
        "fixture_speaker_status_is_authority=false candidate_only=true semantic_promotion=false",
        file=sys.stderr,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
