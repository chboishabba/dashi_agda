#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
import sys
from copy import deepcopy
from pathlib import Path
from typing import Any

SCHEMA = "slr-canonical-claim-projection-v2"
TARGET_SCHEMA = "sl.candidate_world_model.v0_1"


def read_jsonl(path: Path) -> list[dict[str, Any]]:
    return [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines() if line.strip()]


def integer(value: Any) -> int | None:
    try:
        return int(value)
    except (TypeError, ValueError):
        return None


def node_sentence(node: dict[str, Any]) -> int | None:
    metadata = node.get("metadata")
    return integer(metadata.get("sentence")) if isinstance(metadata, dict) else None


def source_sha(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def unique_interval(text: str, phrase: str) -> tuple[int, int] | None:
    if not phrase:
        return None
    first = text.find(phrase)
    if first < 0 or text.find(phrase, first + 1) >= 0:
        return None
    return first, first + len(phrase)


def overlaps(a0: int, a1: int, b0: int, b1: int) -> bool:
    return a0 < b1 and b0 < a1


def candidate_span_nodes(claims: list[dict[str, Any]]) -> list[dict[str, Any]]:
    return [n for n in claims if isinstance(n, dict) and n.get("node_kind") == "discourse_span_candidate"]


def claim_node(claim_ref: str, fixture: dict[str, Any], exact_span: dict[str, Any] | None) -> dict[str, Any]:
    current_status = fixture.get("current_primary_status", "unresolved")
    return {
        "node_id": f"canonical-claim:{claim_ref}",
        "node_kind": "canonical_claim_reference",
        "label": claim_ref,
        "status": "candidate",
        "source_anchor_ids": [claim_ref],
        "conflict_ids": [],
        "promotion_status": "reference_only",
        "residual": {
            "exact_span_weld": "paid" if exact_span else "unpaid",
            "speaker_status_from_historical_fixture_used_as_authority": False,
        },
        "metadata": {
            "claim_ref": claim_ref,
            "parser_sentence_ids": fixture.get("parser_sentence_ids", []),
            "text_role": fixture.get("text_role", ""),
            "historical_candidate_status": fixture.get("candidate_status", ""),
            "historical_candidate_speaker": fixture.get("candidate_speaker", ""),
            "current_primary_speaker": fixture.get("current_primary_speaker", ""),
            "current_primary_status": current_status,
            "current_primary_evidence_kind": fixture.get("current_primary_evidence_kind", ""),
            "current_primary_source_stable_id": fixture.get("current_primary_source_stable_id", ""),
            "historical_candidate_state_rewritten": bool(fixture.get("historical_candidate_state_rewritten", False)),
            "exact_source_span": exact_span,
            "semantic_promotion": False,
        },
    }


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser()
    p.add_argument("--world", type=Path, required=True)
    p.add_argument("--fixture", type=Path, required=True)
    p.add_argument("--cuts", type=Path, required=True)
    p.add_argument("--source", type=Path)
    p.add_argument("--source-metadata", type=Path)
    p.add_argument("--output", type=Path, required=True)
    return p.parse_args()


def main() -> int:
    args = parse_args()
    world = json.loads(args.world.read_text(encoding="utf-8"))
    if world.get("schema_version") != TARGET_SCHEMA:
        raise SystemExit(f"unexpected world schema: {world.get('schema_version')!r}")
    if bool((world.get("metadata") or {}).get("semantic_promotion", False)):
        raise SystemExit("claim projection refuses semantically promoted input")

    source_text = None
    source_meta: dict[str, Any] = {}
    source_digest = ""
    if args.source or args.source_metadata:
        if not (args.source and args.source_metadata):
            raise SystemExit("--source and --source-metadata must be supplied together")
        source_text = args.source.read_text(encoding="utf-8")
        source_meta = json.loads(args.source_metadata.read_text(encoding="utf-8"))
        source_digest = source_sha(source_text)
        expected = str(source_meta.get("transcript_sha256", ""))
        if source_digest != expected:
            raise SystemExit("source transcript SHA mismatch")
        if str((world.get("metadata") or {}).get("source_sha256", "")) != source_digest:
            raise SystemExit("world model and source transcript are not same-object")

    fixtures = read_jsonl(args.fixture)
    cuts = read_jsonl(args.cuts)
    out = deepcopy(world)
    claims = list(out.get("claims") or [])
    relations = list(out.get("relations") or [])
    existing_ids = {str(n.get("node_id", "")) for n in claims if isinstance(n, dict)}
    relation_ids = {str(e.get("relation_id", "")) for e in relations if isinstance(e, dict)}
    spans = candidate_span_nodes(claims)

    sentence_to_claims: dict[int, set[str]] = {}
    exact_spans: dict[str, dict[str, Any]] = {}
    unresolved_exact: list[str] = []

    for fixture in fixtures:
        ref = str(fixture.get("claim_ref", ""))
        if not ref:
            continue
        for sentence in [s for s in (integer(v) for v in fixture.get("parser_sentence_ids", [])) if s is not None]:
            sentence_to_claims.setdefault(sentence, set()).add(ref)
        if source_text is not None and fixture.get("source_phrase"):
            interval = unique_interval(source_text, str(fixture["source_phrase"]))
            if interval is None:
                unresolved_exact.append(ref)
            else:
                start, end = interval
                covered = []
                for span in spans:
                    md = span.get("metadata") or {}
                    s0, s1 = integer(md.get("char_start")), integer(md.get("char_end"))
                    if s0 is not None and s1 is not None and overlaps(start, end, s0, s1):
                        covered.append(str(span.get("node_id", "")))
                if covered:
                    exact_spans[ref] = {
                        "source_sha256": source_digest,
                        "char_start": start,
                        "char_end": end,
                        "source_phrase": fixture["source_phrase"],
                        "candidate_span_ids": covered,
                        "same_source_object": True,
                        "unique_bounded_phrase": True,
                    }
                else:
                    unresolved_exact.append(ref)

    added_claim_refs = 0
    for fixture in fixtures:
        ref = str(fixture.get("claim_ref", ""))
        if not ref:
            continue
        cid = f"canonical-claim:{ref}"
        if cid not in existing_ids:
            claims.append(claim_node(ref, fixture, exact_spans.get(ref)))
            existing_ids.add(cid)
            added_claim_refs += 1

    added_edges = 0
    ambiguous_edges = 0
    exact_edges = 0
    discourse_nodes = [n for n in claims if isinstance(n, dict) and n.get("node_kind") in {"discourse_span_candidate", "discourse_boundary_candidate"}]

    for fixture in fixtures:
        ref = str(fixture.get("claim_ref", ""))
        if not ref:
            continue
        target = f"canonical-claim:{ref}"
        exact = exact_spans.get(ref)
        exact_ids = set(exact.get("candidate_span_ids", [])) if exact else set()
        sentence_ids = {s for s in (integer(v) for v in fixture.get("parser_sentence_ids", [])) if s is not None}
        for node in discourse_nodes:
            source_id = str(node.get("node_id", ""))
            sentence = node_sentence(node)
            exact_match = source_id in exact_ids
            sentence_match = sentence is not None and sentence in sentence_ids
            if not (exact_match or sentence_match):
                continue
            rid = f"claim-projection:{source_id}:{ref}"
            if not source_id or rid in relation_ids:
                continue
            competing = sorted(sentence_to_claims.get(sentence, set())) if sentence is not None else []
            ambiguous = (not exact_match) and len(competing) > 1
            relations.append({
                "relation_id": rid,
                "source_id": source_id,
                "target_id": target,
                "relation_kind": "candidate_projection_to_canonical_claim",
                "status": "candidate" if exact_match else ("conflicted" if ambiguous else "candidate"),
                "source_anchor_ids": list(node.get("source_anchor_ids") or []),
                "promotion_status": "candidate_only",
                "residual": {
                    "exact_span_weld": "paid" if exact_match else "unpaid",
                    "competing_claim_refs_for_sentence": [] if exact_match else competing,
                    "requires_labelled_alignment_or_exact_cut_receipt": ambiguous and not exact_match,
                },
                "metadata": {
                    "schema": SCHEMA,
                    "parser_sentence_id": sentence,
                    "claim_ref": ref,
                    "mapping_basis": "same-source unique bounded phrase + offsets" if exact_match else "explicit repo fixture parser_sentence_ids",
                    "current_primary_speaker": fixture.get("current_primary_speaker", ""),
                    "current_primary_status": fixture.get("current_primary_status", ""),
                    "historical_fixture_speaker_used_as_authority": False,
                    "semantic_promotion": False,
                },
            })
            relation_ids.add(rid)
            added_edges += 1
            exact_edges += int(exact_match)
            ambiguous_edges += int(ambiguous)

    cut_constraints = [{
        "sentence_ref": row.get("sentence_ref", ""),
        "left_claim": row.get("left_claim", ""),
        "right_claim": row.get("right_claim", ""),
        "cut_anchor": row.get("cut_anchor", ""),
        "historical_status": row.get("status", row.get("left_status", "")),
        "verification_required_in_fixture": bool(row.get("verification_required", False)),
        "role": "claim projection disambiguation constraint",
        "semantic_promotion": False,
    } for row in cuts if row.get("left_claim") and row.get("right_claim")]

    meta = dict(out.get("metadata") or {})
    meta["canonical_claim_projection"] = {
        "schema": SCHEMA,
        "fixture": str(args.fixture),
        "cuts": str(args.cuts),
        "source": str(args.source) if args.source else "unsupplied",
        "source_metadata": str(args.source_metadata) if args.source_metadata else "unsupplied",
        "source_sha256": source_digest,
        "stable_source_id": (source_meta.get("ibrahim") or {}).get("stable_source_id", "") if source_meta else "",
        "dewey_parent": (source_meta.get("ibrahim") or {}).get("dewey_parent", "") if source_meta else "",
        "doi_state": (((source_meta.get("ibrahim") or {}).get("doi") or {}).get("state", "")) if source_meta else "",
        "qid_role": (source_meta.get("ibrahim") or {}).get("qid_role", "") if source_meta else "",
        "historical_fixture_speaker_status_is_authority": False,
        "primary_speaker_resolution_is_claim_relative": True,
        "exact_subspan_weld_paid_only_by_same_source_unique_phrase_offsets": True,
        "unresolved_exact_claim_refs": sorted(set(unresolved_exact)),
        "cut_constraints": cut_constraints,
        "semantic_promotion": False,
        "candidate_only": True,
    }
    out["metadata"] = meta
    out["claims"] = claims
    out["relations"] = relations

    summary = dict(out.get("summary") or {})
    summary.update({
        "canonical_claim_reference_count": added_claim_refs,
        "candidate_claim_projection_edge_count": added_edges,
        "exact_subspan_projection_edge_count": exact_edges,
        "ambiguous_sentence_projection_edge_count": ambiguous_edges,
        "exact_subspan_claim_count": len(exact_spans),
        "unresolved_exact_subspan_claim_count": len(set(unresolved_exact)),
        "claim_projection_cut_constraint_count": len(cut_constraints),
    })
    out["summary"] = summary

    status_counts = {"candidate": 0, "conflicted": 0}
    for collection in (claims, relations):
        for item in collection:
            status = str(item.get("status", "")) if isinstance(item, dict) else ""
            if status in status_counts:
                status_counts[status] += 1
    out["status_counts"] = status_counts

    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(out, indent=2, ensure_ascii=False, sort_keys=True) + "\n", encoding="utf-8")
    print(
        "SLR_CANONICAL_CLAIM_PROJECTION_RECEIPT "
        f"schema={SCHEMA} target={TARGET_SCHEMA} claim_refs={added_claim_refs} "
        f"projection_edges={added_edges} exact_edges={exact_edges} exact_claims={len(exact_spans)} "
        f"ambiguous_sentence_edges={ambiguous_edges} unresolved_exact={len(set(unresolved_exact))} "
        "historical_fixture_speaker_is_authority=false candidate_only=true semantic_promotion=false",
        file=sys.stderr,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
