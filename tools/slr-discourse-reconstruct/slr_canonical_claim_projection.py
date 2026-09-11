#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path
from typing import Any

SCHEMA = "slr-canonical-claim-projection-v1"

# Deliberately small, high-value projection surface.  Each phrase is copied from
# the tracked primary ABC transcript and must occur exactly once.  The adapter
# projects source spans onto existing candidate nodes; it never manufactures a
# canonical claim from lexical similarity or model output.
CLAIMS: list[dict[str, str]] = [
    {
        "claim_id": "ABC730-2026-09-09-C017",
        "speaker": "JACOB GREBER / UK government",
        "claim_role": "policyPosition",
        "phrase": "Britain is now moving to impose an \"import ban on goods from illegal settlements in the occupied territories\".",
    },
    {
        "claim_id": "ABC730-2026-09-09-C028",
        "speaker": "PENNY WONG",
        "claim_role": "policyPosition",
        "phrase": "Australia is not, at this time, pursuing a blanket-style import ban.",
    },
    {
        "claim_id": "ABC730-2026-09-09-C029",
        "speaker": "PENNY WONG",
        "claim_role": "policyPosition",
        "phrase": "We have concerns about the implementation of a blanket ban and unintended consequences for Australian businesses for Palestinians and for Israelis.",
    },
    {
        "claim_id": "ABC730-2026-09-09-C030",
        "speaker": "ED HUSIC",
        "claim_role": "policyPosition",
        "phrase": "We can't say we are for the state of Palestine, which I'm very much a supporter of, and ignore the fact that the illegal settlements are undermining the ability for a state of Palestine to emerge.",
    },
    {
        "claim_id": "ABC730-2026-09-09-C031",
        "speaker": "ED HUSIC",
        "claim_role": "policyPosition",
        "phrase": "We need to take action.",
    },
    {
        "claim_id": "ABC730-2026-09-09-C032",
        "speaker": "DAVID SHOEBRIDGE",
        "claim_role": "evaluativeRhetoric",
        "phrase": "This is unbelievable gaslighting from Labor.",
    },
    {
        "claim_id": "ABC730-2026-09-09-C033",
        "speaker": "JULIAN LEESER",
        "claim_role": "causalOrPredictive",
        "phrase": "the question is whether any of these sanctions actually lead you towards a two-state solution and I'm not sure that they do.",
    },
    {
        "claim_id": "ABC730-2026-09-09-C035",
        "speaker": "PENNY WONG / Australian government",
        "claim_role": "policyPosition",
        "phrase": "Right now, Australians can’t trade with sanctioned individuals or entities in the West Bank.",
    },
    {
        "claim_id": "ABC730-2026-09-09-C040",
        "speaker": "JACOB GREBER / Australian government",
        "claim_role": "policyPosition",
        "phrase": "Australia’s official position is to pursue “further targeted measures” against what it calls “illegal settlements and settler violence”.",
    },
    {
        "claim_id": "ABC730-2026-09-09-C041",
        "speaker": "PENNY WONG / Australian government",
        "claim_role": "causalOrPredictive",
        "phrase": "the rapid expansion of settlements, the proposed E1 settlement development and flagrant settler violence are extinguishing the possibility of a two-state solution",
    },
    {
        "claim_id": "ABC730-2026-09-09-C042",
        "speaker": "PENNY WONG / Australian government",
        "claim_role": "policyPosition",
        "phrase": "that remains the only path to enduring peace and security for Israelis and Palestinians.",
    },
]


def load_json(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise SystemExit(f"expected JSON object: {path}")
    return value


def sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def unique_interval(source: str, phrase: str) -> tuple[int, int] | None:
    first = source.find(phrase)
    if first < 0:
        return None
    if source.find(phrase, first + 1) >= 0:
        return None
    return first, first + len(phrase)


def span_candidates(model: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        row for row in model.get("claims", [])
        if row.get("node_kind") == "discourse_span_candidate"
        and isinstance(row.get("metadata"), dict)
    ]


def overlaps(a0: int, a1: int, b0: int, b1: int) -> bool:
    return a0 < b1 and b0 < a1


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser()
    p.add_argument("--source", type=Path, required=True)
    p.add_argument("--source-metadata", type=Path, required=True)
    p.add_argument("--world-model", type=Path, required=True)
    p.add_argument("--output", type=Path, required=True)
    return p.parse_args()


def main() -> int:
    args = parse_args()
    source = args.source.read_text(encoding="utf-8")
    source_meta = load_json(args.source_metadata)
    model = load_json(args.world_model)

    actual_sha = sha256_text(source)
    expected_sha = str(source_meta.get("transcript_sha256", ""))
    if not expected_sha or actual_sha != expected_sha:
        raise SystemExit("source transcript SHA does not match tracked primary-source metadata")
    if model.get("schema_version") != "sl.candidate_world_model.v0_1":
        raise SystemExit("unexpected CandidateWorldModel schema")
    if (model.get("metadata") or {}).get("source_sha256") != actual_sha:
        raise SystemExit("CandidateWorldModel is not derived from the same source transcript")
    if bool((model.get("metadata") or {}).get("semantic_promotion", False)):
        raise SystemExit("claim projection refuses a semantically promoted input model")

    spans = span_candidates(model)
    projections: list[dict[str, Any]] = []
    unresolved: list[dict[str, Any]] = []

    for spec in CLAIMS:
        interval = unique_interval(source, spec["phrase"])
        if interval is None:
            unresolved.append({
                "claim_id": spec["claim_id"],
                "status": "unresolved-source-phrase",
                "reason": "bounded primary-source phrase missing or non-unique",
            })
            continue
        start, end = interval
        covered = []
        for span in spans:
            md = span.get("metadata") or {}
            s0 = int(md.get("char_start", 0))
            s1 = int(md.get("char_end", 0))
            if overlaps(start, end, s0, s1):
                covered.append({
                    "candidate_id": span.get("node_id", ""),
                    "char_start": s0,
                    "char_end": s1,
                    "sentence": md.get("sentence"),
                    "segment_index": md.get("segment_index"),
                    "candidate_status": span.get("status", ""),
                    "promotion_status": span.get("promotion_status", ""),
                })
        if not covered:
            unresolved.append({
                "claim_id": spec["claim_id"],
                "status": "unresolved-candidate-coverage",
                "source_char_start": start,
                "source_char_end": end,
                "reason": "source phrase is paid but no candidate span overlaps its source interval",
            })
            continue
        projections.append({
            "claim_id": spec["claim_id"],
            "projection_kind": "same-source-bounded-span-projection",
            "source_sha256": actual_sha,
            "source_char_start": start,
            "source_char_end": end,
            "source_phrase": spec["phrase"],
            "speaker_or_attributor": spec["speaker"],
            "claim_role": spec["claim_role"],
            "candidate_ids": [row["candidate_id"] for row in covered],
            "candidate_coverage": covered,
            "same_source_object": True,
            "bounded_source_phrase_unique": True,
            "speaker_attribution_source_role": "speaker-labelled-primary-programme-transcript",
            "canonical_claim_truth_promoted": False,
            "semantic_promotion": False,
            "candidate_only": True,
        })

    output = {
        "schema": SCHEMA,
        "target_schema": "sl.candidate_world_model.v0_1",
        "source_sha256": actual_sha,
        "source_stable_id": (source_meta.get("ibrahim") or {}).get("stable_source_id", ""),
        "dewey_parent": (source_meta.get("ibrahim") or {}).get("dewey_parent", ""),
        "dewey_role": (source_meta.get("ibrahim") or {}).get("dewey_role", ""),
        "doi_state": ((source_meta.get("ibrahim") or {}).get("doi") or {}).get("state", ""),
        "qid_role": (source_meta.get("ibrahim") or {}).get("qid_role", ""),
        "projection_count": len(projections),
        "unresolved_count": len(unresolved),
        "projections": projections,
        "unresolved": unresolved,
        "rules": {
            "projection_requires_same_source_sha": True,
            "projection_requires_unique_bounded_source_phrase": True,
            "lexical_similarity_fallback": False,
            "qid_dewey_doi_create_claim_truth": False,
            "projection_promotes_truth": False,
            "historical_claim_ledger_rewritten": False,
        },
        "semantic_promotion": False,
        "candidate_only": True,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(output, indent=2, ensure_ascii=False, sort_keys=True) + "\n", encoding="utf-8")
    print(
        "SLR_CANONICAL_CLAIM_PROJECTION_RECEIPT "
        f"schema={SCHEMA} source_sha256={actual_sha} projections={len(projections)} "
        f"unresolved={len(unresolved)} same_source_required=true unique_phrase_required=true "
        "semantic_promotion=false candidate_only=true",
        file=sys.stderr,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
