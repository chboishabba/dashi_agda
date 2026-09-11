#!/usr/bin/env python3
from __future__ import annotations

import argparse
import csv
import json
import re
import sys
from pathlib import Path
from typing import Any

SCHEMA = "slr-labelled-discourse-path-v1"
WORD_RE = re.compile(r"[A-Za-z0-9]+(?:['’][A-Za-z0-9]+)?")


def intval(value: Any) -> int | None:
    try:
        return int(str(value))
    except (TypeError, ValueError):
        return None


def speaker_key(value: str) -> str:
    return " ".join(value.lower().replace("dame ", "").split())


def state_for(confidence: str) -> str:
    if confidence == "exact-neighbour":
        return "exact"
    if confidence in {"local", "weak"}:
        return "bounded"
    return "unpaid"


def parser_sentence_ranges(path: Path) -> dict[int, tuple[int, int]]:
    out: dict[int, tuple[int, int]] = {}
    for raw in path.read_text(encoding="utf-8").splitlines():
        p = raw.split("\t")
        if len(p) >= 4 and p[0] == "S":
            sid = intval(p[1]); start = intval(p[2]); end = intval(p[3])
            if sid is not None and start is not None and end is not None:
                out[sid] = (start, end)
    return out


def word_char_starts(text: str) -> list[int]:
    return [m.start() for m in WORD_RE.finditer(text)]


def read_gold(path: Path) -> list[dict[str, str]]:
    with path.open("r", encoding="utf-8", newline="") as handle:
        return list(csv.DictReader(handle, delimiter="\t"))


def read_jsonl(path: Path) -> list[dict[str, Any]]:
    return [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines() if line.strip()]


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser()
    p.add_argument("--source", type=Path, required=True)
    p.add_argument("--parser", type=Path, required=True)
    p.add_argument("--gold-boundaries", type=Path, required=True)
    p.add_argument("--cuts", type=Path, required=True)
    p.add_argument("--output-json", type=Path, required=True)
    p.add_argument("--output-tsv", type=Path, required=True)
    return p.parse_args()


def main() -> int:
    args = parse_args()
    source = args.source.read_text(encoding="utf-8")
    starts = word_char_starts(source)
    sentence_ranges = parser_sentence_ranges(args.parser)
    gold = read_gold(args.gold_boundaries)
    cuts = [row for row in read_jsonl(args.cuts) if row.get("left_claim") and row.get("right_claim")]

    gold_by_sentence: dict[int, list[dict[str, str]]] = {}
    for row in gold:
        sid = intval(row.get("parser_sentence"))
        if sid is not None:
            gold_by_sentence.setdefault(sid, []).append(row)
    for rows in gold_by_sentence.values():
        rows.sort(key=lambda row: intval(row.get("unlabelled_word_position")) or 10**9)

    paths: list[dict[str, Any]] = []
    direct = multihop = exact_hops = bounded_hops = unpaid_hops = 0

    for cut in cuts:
        sentence_ref = str(cut.get("sentence_ref", ""))
        m = re.fullmatch(r"spaCy-(\d+)", sentence_ref)
        sid = int(m.group(1)) if m else None
        left = speaker_key(str(cut.get("left_speaker", "")))
        right = speaker_key(str(cut.get("right_speaker", "")))
        sentence_range = sentence_ranges.get(sid) if sid is not None else None

        candidate_rows = gold_by_sentence.get(sid, []) if sid is not None else []
        paths_from_left: list[list[dict[str, str]]] = []
        for i, row in enumerate(candidate_rows):
            if speaker_key(row.get("left_speaker", "")) != left:
                continue
            path: list[dict[str, str]] = []
            current = left
            for j in range(i, len(candidate_rows)):
                hop = candidate_rows[j]
                if speaker_key(hop.get("left_speaker", "")) != current:
                    break
                path.append(hop)
                current = speaker_key(hop.get("right_speaker", ""))
                if current == right:
                    paths_from_left.append(path.copy())
                    break

        chosen = min(paths_from_left, key=len) if paths_from_left else []
        if len(chosen) == 1:
            direct += 1
        elif len(chosen) > 1:
            multihop += 1

        hops: list[dict[str, Any]] = []
        boundaries: list[int] = []
        for row in chosen:
            confidence = row.get("alignment_confidence", "unmapped")
            state = state_for(confidence)
            word_pos = intval(row.get("unlabelled_word_position"))
            boundary_char = None
            if word_pos is not None and 0 <= word_pos < len(starts) and sentence_range is not None:
                candidate_char = starts[word_pos]
                if sentence_range[0] < candidate_char < sentence_range[1]:
                    boundary_char = candidate_char
            if boundary_char is None:
                state = "unpaid"
            else:
                boundaries.append(boundary_char)
            if state == "exact": exact_hops += 1
            elif state == "bounded": bounded_hops += 1
            else: unpaid_hops += 1
            hops.append({
                "gold_id": row.get("gold_id", ""),
                "left_speaker": row.get("left_speaker", ""),
                "right_speaker": row.get("right_speaker", ""),
                "alignment_confidence": confidence,
                "weld_state": state,
                "boundary_char": boundary_char,
                "matched_hard_node": row.get("matched_hard_node", ""),
                "matched_risk_node": row.get("matched_risk_node", ""),
            })

        segment_speakers: list[str] = []
        if chosen:
            segment_speakers = [chosen[0].get("left_speaker", "")] + [r.get("right_speaker", "") for r in chosen]
        segments: list[dict[str, Any]] = []
        if sentence_range is not None and chosen and all(h["boundary_char"] is not None for h in hops):
            cuts_chars = [sentence_range[0]] + [int(h["boundary_char"]) for h in hops] + [sentence_range[1]]
            for idx in range(len(cuts_chars) - 1):
                segments.append({
                    "segment_index": idx,
                    "speaker": segment_speakers[idx] if idx < len(segment_speakers) else "",
                    "char_start": cuts_chars[idx],
                    "char_end": cuts_chars[idx + 1],
                    "boundary_before_state": "sentence-start" if idx == 0 else hops[idx - 1]["weld_state"],
                    "boundary_after_state": "sentence-end" if idx == len(cuts_chars) - 2 else hops[idx]["weld_state"],
                })

        path_state = "unpaid"
        if chosen:
            states = [h["weld_state"] for h in hops]
            if all(s == "exact" for s in states):
                path_state = "exact"
            elif all(s in {"exact", "bounded"} for s in states):
                path_state = "bounded"

        intermediate = segment_speakers[1:-1] if len(segment_speakers) > 2 else []
        paths.append({
            "sentence_ref": sentence_ref,
            "parser_sentence": sid,
            "left_claim": cut.get("left_claim", ""),
            "right_claim": cut.get("right_claim", ""),
            "requested_left_speaker": cut.get("left_speaker", ""),
            "requested_right_speaker": cut.get("right_speaker", ""),
            "path_state": path_state,
            "hop_count": len(hops),
            "direct_handoff": len(hops) == 1,
            "intermediate_speakers": intermediate,
            "skip_edge_permitted": len(intermediate) == 0,
            "hops": hops,
            "segments": segments,
            "semantic_promotion": False,
            "claim_truth_promoted": False,
        })

    report = {
        "schema": SCHEMA,
        "candidate_only": True,
        "semantic_promotion": False,
        "claim_truth_promoted": False,
        "skip_intermediate_speaker_forbidden": True,
        "summary": {
            "paths": len(paths),
            "direct_paths": direct,
            "multihop_paths": multihop,
            "exact_hops": exact_hops,
            "bounded_hops": bounded_hops,
            "unpaid_hops": unpaid_hops,
        },
        "paths": paths,
    }
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_tsv.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    with args.output_tsv.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.writer(handle, delimiter="\t", lineterminator="\n")
        writer.writerow(["schema","sentence_ref","left_claim","right_claim","path_state","hop_count","direct_handoff","intermediate_speakers","skip_edge_permitted","candidate_only"])
        for row in paths:
            writer.writerow([
                SCHEMA,row["sentence_ref"],row["left_claim"],row["right_claim"],row["path_state"],row["hop_count"],
                str(row["direct_handoff"]).lower(),",".join(row["intermediate_speakers"]),str(row["skip_edge_permitted"]).lower(),"true",
            ])

    print(
        "SLR_LABELLED_DISCOURSE_PATH_RECEIPT "
        f"schema={SCHEMA} paths={len(paths)} direct={direct} multihop={multihop} "
        f"exact_hops={exact_hops} bounded_hops={bounded_hops} unpaid_hops={unpaid_hops} "
        "skip_intermediate_speaker_forbidden=true candidate_only=true semantic_promotion=false claim_truth_promoted=false",
        file=sys.stderr,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
