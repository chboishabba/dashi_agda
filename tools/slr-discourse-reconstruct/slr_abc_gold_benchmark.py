#!/usr/bin/env python3
from __future__ import annotations

import argparse
import csv
import json
import re
import sys
from dataclasses import dataclass
from difflib import SequenceMatcher
from pathlib import Path
from typing import Any

SCHEMA = "slr-abc-gold-benchmark-v1"
WORD_RE = re.compile(r"[A-Za-z0-9]+(?:['’][A-Za-z0-9]+)?")


def words(text: str) -> list[str]:
    return [m.group(0).lower().replace("’", "'") for m in WORD_RE.finditer(text)]


def boolv(value: str | None) -> bool:
    return str(value or "").strip().lower() in {"1", "true", "yes"}


def intval(value: str | None) -> int:
    try:
        return int(str(value or "0").strip())
    except ValueError:
        return 0


def explicit_speaker(prefix: str) -> str | None:
    name = prefix.split(",", 1)[0].strip()
    if not name or len(name) > 80:
        return None
    letters = "".join(ch for ch in name if ch.isalpha())
    if not letters or name.upper() != name:
        return None
    if len(name.split()) > 8:
        return None
    return name


@dataclass
class GoldBoundary:
    gold_id: str
    labelled_index: int
    left_speaker: str
    right_speaker: str
    source_position: int | None = None
    alignment_confidence: str = "unmapped"
    hidden_target: bool = False
    parser_sentence: int | None = None
    matched_hard_node: str = ""
    matched_risk_node: str = ""


@dataclass
class ParserUnit:
    sentence: int
    ordinal: int
    word: str


@dataclass
class CandidateBoundary:
    node_id: str
    sentence: int
    split: int
    projection: str
    pareto: list[str]
    hard: bool
    hidden_risk: bool
    false_cut_risk: bool
    position: int | None


def extract_labelled_speaker_words(text: str) -> tuple[list[str], list[str], list[GoldBoundary]]:
    labelled_words: list[str] = []
    speakers: list[str] = []
    current_speaker = ""
    paragraphs = [p.strip() for p in re.split(r"\n\s*\n", text) if p.strip()]
    for paragraph in paragraphs:
        content = paragraph
        if ":" in paragraph:
            prefix, rest = paragraph.split(":", 1)
            speaker = explicit_speaker(prefix)
            if speaker:
                current_speaker = speaker
                content = rest.strip()
        for token in words(content):
            labelled_words.append(token)
            speakers.append(current_speaker or "UNLABELLED")

    boundaries: list[GoldBoundary] = []
    for i in range(1, len(labelled_words)):
        if speakers[i] != speakers[i - 1] and speakers[i] != "UNLABELLED" and speakers[i - 1] != "UNLABELLED":
            boundaries.append(
                GoldBoundary(
                    gold_id=f"gold-speaker-{len(boundaries)+1:03d}",
                    labelled_index=i,
                    left_speaker=speakers[i - 1],
                    right_speaker=speakers[i],
                )
            )
    return labelled_words, speakers, boundaries


def exact_mapping(left: list[str], right: list[str]) -> dict[int, int]:
    matcher = SequenceMatcher(a=left, b=right, autojunk=False)
    mapping: dict[int, int] = {}
    for block in matcher.get_matching_blocks():
        for offset in range(block.size):
            mapping[block.a + offset] = block.b + offset
    return mapping


def map_gold_boundaries(
    boundaries: list[GoldBoundary], mapping: dict[int, int], labelled_len: int, max_gap: int
) -> None:
    for boundary in boundaries:
        i = boundary.labelled_index
        left = None
        right = None
        left_distance = None
        right_distance = None
        for d in range(0, max_gap + 1):
            j = i - 1 - d
            if j >= 0 and j in mapping:
                left = mapping[j]
                left_distance = d
                break
        for d in range(0, max_gap + 1):
            j = i + d
            if j < labelled_len and j in mapping:
                right = mapping[j]
                right_distance = d
                break
        if left is None or right is None or left >= right:
            continue
        boundary.source_position = right
        total_gap = int(left_distance or 0) + int(right_distance or 0)
        if total_gap == 0:
            boundary.alignment_confidence = "exact-neighbour"
        elif total_gap <= 4:
            boundary.alignment_confidence = "local"
        else:
            boundary.alignment_confidence = "weak"


def parse_parser(path: Path) -> list[ParserUnit]:
    units: list[ParserUnit] = []
    current_sentence: int | None = None
    for raw in path.read_text(encoding="utf-8").splitlines():
        p = raw.split("\t")
        if not p:
            continue
        if p[0] == "S" and len(p) > 1:
            current_sentence = intval(p[1])
        elif p[0] == "E":
            current_sentence = None
        elif p[0] == "T" and current_sentence is not None and len(p) > 5:
            ordinal = intval(p[1])
            for token in words(p[5]):
                units.append(ParserUnit(current_sentence, ordinal, token))
    return units


def map_parser_units(units: list[ParserUnit], source_words: list[str]) -> tuple[dict[int, int], dict[int, tuple[int, int]]]:
    mapping = exact_mapping([u.word for u in units], source_words)
    intervals: dict[int, list[int]] = {}
    for idx, source_idx in mapping.items():
        intervals.setdefault(units[idx].sentence, []).append(source_idx)
    bounded = {sentence: (min(xs), max(xs)) for sentence, xs in intervals.items() if xs}
    return mapping, bounded


def candidate_position(
    sentence: int,
    split: int,
    units: list[ParserUnit],
    parser_mapping: dict[int, int],
) -> int | None:
    left: list[int] = []
    right: list[int] = []
    for idx, unit in enumerate(units):
        if unit.sentence != sentence or idx not in parser_mapping:
            continue
        pos = parser_mapping[idx]
        if unit.ordinal < split:
            left.append(pos)
        else:
            right.append(pos)
    if not left or not right:
        return None
    l = max(left)
    r = min(right)
    if l >= r:
        return None
    return r


def read_quality(path: Path, units: list[ParserUnit], parser_mapping: dict[int, int]) -> list[CandidateBoundary]:
    out: list[CandidateBoundary] = []
    with path.open("r", encoding="utf-8", newline="") as handle:
        for row in csv.DictReader(handle, delimiter="\t"):
            sentence = intval(row.get("sentence"))
            split = intval(row.get("split"))
            out.append(
                CandidateBoundary(
                    node_id=row.get("node_id", ""),
                    sentence=sentence,
                    split=split,
                    projection=row.get("projection", ""),
                    pareto=[x for x in row.get("pareto_fibres", "").split(",") if x],
                    hard=boolv(row.get("hard_cut_admissible")),
                    hidden_risk=boolv(row.get("hidden_speaker_splice_risk")),
                    false_cut_risk=boolv(row.get("false_cut_risk")),
                    position=candidate_position(sentence, split, units, parser_mapping),
                )
            )
    return out


def classify_hidden_gold(boundaries: list[GoldBoundary], intervals: dict[int, tuple[int, int]], margin: int) -> None:
    for boundary in boundaries:
        if boundary.source_position is None:
            continue
        p = boundary.source_position
        containing = [
            (sentence, lo, hi)
            for sentence, (lo, hi) in intervals.items()
            if lo <= p <= hi
        ]
        if not containing:
            continue
        sentence, lo, hi = min(containing, key=lambda x: (x[2] - x[1], x[0]))
        boundary.parser_sentence = sentence
        boundary.hidden_target = (p - lo) > margin and (hi - p) > margin


def greedy_match(
    gold: list[GoldBoundary], candidates: list[CandidateBoundary], tolerance: int
) -> tuple[dict[str, str], set[str]]:
    pairs: list[tuple[int, str, str]] = []
    for g in gold:
        if g.source_position is None:
            continue
        for c in candidates:
            if c.position is None:
                continue
            distance = abs(g.source_position - c.position)
            if distance <= tolerance:
                pairs.append((distance, g.gold_id, c.node_id))
    pairs.sort()
    g_used: set[str] = set()
    c_used: set[str] = set()
    matched: dict[str, str] = {}
    for _, gid, cid in pairs:
        if gid in g_used or cid in c_used:
            continue
        g_used.add(gid)
        c_used.add(cid)
        matched[gid] = cid
    return matched, c_used


def ratio_milli(num: int, den: int) -> int | None:
    if den == 0:
        return None
    return round(1000 * num / den)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--unlabelled-source", type=Path, required=True)
    parser.add_argument("--labelled-source", type=Path, required=True)
    parser.add_argument("--parser", type=Path, required=True)
    parser.add_argument("--quality", type=Path, required=True)
    parser.add_argument("--span-stderr", type=Path)
    parser.add_argument("--output-json", type=Path, required=True)
    parser.add_argument("--output-tsv", type=Path, required=True)
    parser.add_argument("--gold-gap", type=int, default=12)
    parser.add_argument("--match-tolerance", type=int, default=6)
    parser.add_argument("--sentence-margin", type=int, default=1)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    labelled_text = args.labelled_source.read_text(encoding="utf-8")
    unlabelled_text = args.unlabelled_source.read_text(encoding="utf-8")
    labelled_words, _, gold = extract_labelled_speaker_words(labelled_text)
    unlabelled_words = words(unlabelled_text)
    source_mapping = exact_mapping(labelled_words, unlabelled_words)
    map_gold_boundaries(gold, source_mapping, len(labelled_words), args.gold_gap)

    parser_units = parse_parser(args.parser)
    parser_mapping, intervals = map_parser_units(parser_units, unlabelled_words)
    classify_hidden_gold(gold, intervals, args.sentence_margin)
    candidates = read_quality(args.quality, parser_units, parser_mapping)

    hidden_gold = [g for g in gold if g.hidden_target and g.source_position is not None]
    hard_speaker = [c for c in candidates if c.hard and c.projection == "speaker" and c.position is not None]
    risk_candidates = [
        c for c in candidates
        if c.position is not None and (c.hidden_risk or (c.projection == "unresolved" and "speaker" in c.pareto))
    ]

    hard_match, hard_used = greedy_match(hidden_gold, hard_speaker, args.match_tolerance)
    risk_match, _ = greedy_match(hidden_gold, risk_candidates, args.match_tolerance)
    for g in hidden_gold:
        g.matched_hard_node = hard_match.get(g.gold_id, "")
        g.matched_risk_node = risk_match.get(g.gold_id, "")

    tp = len(hard_match)
    fp = len(hard_speaker) - len(hard_used)
    fn = len(hidden_gold) - tp
    recovered = sum(bool(g.matched_hard_node or g.matched_risk_node) for g in hidden_gold)
    missed = [g for g in hidden_gold if not g.matched_hard_node]
    uncertainty_on_missed = sum(bool(g.matched_risk_node) for g in missed)
    role_preserved = sum(not c.false_cut_risk for c in hard_speaker)

    source_recoverable: bool | None = None
    if args.span_stderr and args.span_stderr.is_file():
        stderr_text = args.span_stderr.read_text(encoding="utf-8", errors="replace")
        if "source_recoverable=true" in stderr_text:
            source_recoverable = True
        elif "source_recoverable=false" in stderr_text:
            source_recoverable = False

    report: dict[str, Any] = {
        "schema": SCHEMA,
        "label_scope": "explicit-speaker-turns-only",
        "semantic_promotion": False,
        "benchmark_promotes_truth": False,
        "alignment": {
            "labelled_word_count": len(labelled_words),
            "unlabelled_word_count": len(unlabelled_words),
            "mapped_labelled_word_count": len(source_mapping),
            "label_to_unlabelled_coverage_milli": ratio_milli(len(source_mapping), len(labelled_words)),
            "parser_word_unit_count": len(parser_units),
            "mapped_parser_unit_count": len(parser_mapping),
            "parser_to_source_coverage_milli": ratio_milli(len(parser_mapping), len(parser_units)),
        },
        "gold": {
            "explicit_speaker_turn_boundaries": len(gold),
            "mapped_speaker_turn_boundaries": sum(g.source_position is not None for g in gold),
            "hidden_within_parser_sentence": len(hidden_gold),
        },
        "speaker_boundary": {
            "hard_speaker_predictions": len(hard_speaker),
            "true_positive": tp,
            "false_positive": fp,
            "false_negative": fn,
            "precision_milli": ratio_milli(tp, tp + fp),
            "recall_milli": ratio_milli(tp, tp + fn),
            "false_cut_rate_milli": ratio_milli(fp, len(hard_speaker)),
        },
        "hidden_splice": {
            "hard_or_uncertain_recovered": recovered,
            "recovery_milli": ratio_milli(recovered, len(hidden_gold)),
            "missed_by_hard_cut": len(missed),
            "missed_hard_but_flagged_uncertain": uncertainty_on_missed,
            "uncertainty_recall_on_hard_misses_milli": ratio_milli(uncertainty_on_missed, len(missed)),
        },
        "role_preservation": {
            "hard_speaker_role_preserved": role_preserved,
            "hard_speaker_role_preservation_milli": ratio_milli(role_preserved, len(hard_speaker)),
        },
        "quote_nesting_accuracy": {
            "status": "not-scored",
            "reason": "official speaker labels do not constitute gold quote/nesting annotation",
        },
        "uncertainty_calibration": {
            "status": "coverage-only-not-probability-calibrated",
            "reason": "runtime exposes residual fibres/risk flags rather than calibrated probabilities",
        },
        "residual_fibre_delta": {
            "status": "not-scored",
            "reason": "requires aligned labelled-vs-unlabelled candidate fibres rather than speaker labels alone",
        },
        "source_recoverability": source_recoverable,
        "parameters": {
            "gold_gap": args.gold_gap,
            "match_tolerance_words": args.match_tolerance,
            "sentence_margin_words": args.sentence_margin,
        },
    }

    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_tsv.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    with args.output_tsv.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.writer(handle, delimiter="\t", lineterminator="\n")
        writer.writerow([
            "schema", "gold_id", "left_speaker", "right_speaker", "labelled_word_index",
            "unlabelled_word_position", "alignment_confidence", "hidden_target", "parser_sentence",
            "matched_hard_node", "matched_risk_node", "candidate_only",
        ])
        for g in gold:
            writer.writerow([
                SCHEMA, g.gold_id, g.left_speaker, g.right_speaker, g.labelled_index,
                "" if g.source_position is None else g.source_position,
                g.alignment_confidence, str(g.hidden_target).lower(),
                "" if g.parser_sentence is None else g.parser_sentence,
                g.matched_hard_node, g.matched_risk_node, "true",
            ])

    sm = report["speaker_boundary"]
    hm = report["hidden_splice"]
    am = report["alignment"]
    print(
        "SLR_ABC_GOLD_BENCHMARK_RECEIPT "
        f"schema={SCHEMA} label_scope=explicit-speaker-turns-only "
        f"alignment_coverage_milli={am['label_to_unlabelled_coverage_milli']} "
        f"gold_turns={report['gold']['explicit_speaker_turn_boundaries']} "
        f"mapped_gold={report['gold']['mapped_speaker_turn_boundaries']} "
        f"hidden_gold={report['gold']['hidden_within_parser_sentence']} "
        f"hard_speaker_predictions={sm['hard_speaker_predictions']} tp={sm['true_positive']} "
        f"fp={sm['false_positive']} fn={sm['false_negative']} "
        f"precision_milli={sm['precision_milli']} recall_milli={sm['recall_milli']} "
        f"hidden_recovery_milli={hm['recovery_milli']} quote_nesting_scored=false "
        "benchmark_promotes_truth=false candidate_only=true",
        file=sys.stderr,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
