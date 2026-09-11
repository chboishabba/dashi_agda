#!/usr/bin/env python3
from __future__ import annotations

import argparse
import csv
import json
import re
import sys
from pathlib import Path
from typing import Any

SCHEMA = "slr-labelled-subspan-weld-v1"
WORD_RE = re.compile(r"[A-Za-z0-9]+(?:['’][A-Za-z0-9]+)?")


def intval(value: Any) -> int | None:
    try:
        return int(str(value))
    except (TypeError, ValueError):
        return None


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


def speaker_key(value: str) -> str:
    return " ".join(value.lower().replace("dame ", "").split())


def state_for(confidence: str) -> str:
    if confidence == "exact-neighbour":
        return "exact"
    if confidence in {"local", "weak"}:
        return "bounded"
    return "unpaid"


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

    welds: list[dict[str, Any]] = []
    exact = bounded = unpaid = 0

    for cut in cuts:
        sentence_ref = str(cut.get("sentence_ref", ""))
        m = re.fullmatch(r"spaCy-(\d+)", sentence_ref)
        sid = int(m.group(1)) if m else None
        left_speaker = speaker_key(str(cut.get("left_speaker", "")))
        right_speaker = speaker_key(str(cut.get("right_speaker", "")))
        match = None
        if sid is not None:
            for row in gold_by_sentence.get(sid, []):
                if speaker_key(row.get("left_speaker", "")) == left_speaker and speaker_key(row.get("right_speaker", "")) == right_speaker:
                    match = row
                    break

        weld_state = "unpaid"
        confidence = "unmapped"
        boundary_char = None
        sentence_start = sentence_end = None
        if match is not None:
            confidence = match.get("alignment_confidence", "unmapped")
            weld_state = state_for(confidence)
            word_pos = intval(match.get("unlabelled_word_position"))
            sentence_range = sentence_ranges.get(sid) if sid is not None else None
            if word_pos is None or word_pos < 0 or word_pos >= len(starts) or sentence_range is None:
                weld_state = "unpaid"
            else:
                boundary_char = starts[word_pos]
                sentence_start, sentence_end = sentence_range
                if not (sentence_start < boundary_char < sentence_end):
                    weld_state = "unpaid"
                    boundary_char = None

        if weld_state == "exact":
            exact += 1
        elif weld_state == "bounded":
            bounded += 1
        else:
            unpaid += 1

        welds.append({
            "sentence_ref": sentence_ref,
            "parser_sentence": sid,
            "left_claim": cut.get("left_claim", ""),
            "right_claim": cut.get("right_claim", ""),
            "left_speaker": cut.get("left_speaker", ""),
            "right_speaker": cut.get("right_speaker", ""),
            "gold_id": "" if match is None else match.get("gold_id", ""),
            "alignment_confidence": confidence,
            "weld_state": weld_state,
            "sentence_char_start": sentence_start,
            "boundary_char": boundary_char,
            "sentence_char_end": sentence_end,
            "left_subspan": None if boundary_char is None else {"char_start": sentence_start, "char_end": boundary_char},
            "right_subspan": None if boundary_char is None else {"char_start": boundary_char, "char_end": sentence_end},
            "matched_hard_node": "" if match is None else match.get("matched_hard_node", ""),
            "matched_risk_node": "" if match is None else match.get("matched_risk_node", ""),
            "cut_anchor": cut.get("cut_anchor", ""),
            "semantic_promotion": False,
            "claim_truth_promoted": False,
        })

    report = {
        "schema": SCHEMA,
        "candidate_only": True,
        "semantic_promotion": False,
        "claim_truth_promoted": False,
        "weld_semantics": {
            "exact": "gold speaker boundary aligned to immediate neighbouring noisy words inside the same parser sentence",
            "bounded": "gold boundary mapped locally/weakly; retain bounded candidate, do not call exact",
            "unpaid": "no usable same-sentence mapped boundary",
        },
        "summary": {"cuts": len(welds), "exact": exact, "bounded": bounded, "unpaid": unpaid},
        "welds": welds,
    }
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_tsv.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    with args.output_tsv.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.writer(handle, delimiter="\t", lineterminator="\n")
        writer.writerow(["schema","sentence_ref","left_claim","right_claim","left_speaker","right_speaker","gold_id","alignment_confidence","weld_state","sentence_char_start","boundary_char","sentence_char_end","matched_hard_node","matched_risk_node","candidate_only"])
        for row in welds:
            writer.writerow([
                SCHEMA,row["sentence_ref"],row["left_claim"],row["right_claim"],row["left_speaker"],row["right_speaker"],row["gold_id"],row["alignment_confidence"],row["weld_state"],
                "" if row["sentence_char_start"] is None else row["sentence_char_start"],
                "" if row["boundary_char"] is None else row["boundary_char"],
                "" if row["sentence_char_end"] is None else row["sentence_char_end"],
                row["matched_hard_node"],row["matched_risk_node"],"true",
            ])

    print(
        "SLR_LABELLED_SUBSPAN_WELD_RECEIPT "
        f"schema={SCHEMA} cuts={len(welds)} exact={exact} bounded={bounded} unpaid={unpaid} "
        "exact_requires_exact_neighbour=true candidate_only=true semantic_promotion=false claim_truth_promoted=false",
        file=sys.stderr,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
