#!/usr/bin/env python3
"""Classify likely Agda failure mode from check logs."""

from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any


FAILURE_CATEGORIES = [
    "stdlib mismatch",
    "missing module/import",
    "unsolved meta",
    "type mismatch",
    "instance search/no candidate",
    "termination",
    "positivity",
    "parse/scope error",
    "timeout",
    "unknown",
]


@dataclass(frozen=True)
class CategoryHit:
    category: str
    line_no: int | None
    source: str
    excerpt: str
    score: int


_CASE_INSENSITIVE = re.IGNORECASE

CATEGORY_PATTERNS: list[tuple[str, list[tuple[str, int]]]] = [
    (
        "timeout",
        [
            (r"\btimeout\b", 5),
            (r"\btimed out\b", 4),
            (r"\balarm clock\b", 3),
            (r"\btime limit\b", 3),
            (r"\bkilled due to timeout\b", 4),
        ],
    ),
    (
        "stdlib mismatch",
        [
            (r"\binterface file .* was produced by an? (?:older|newer) version\b", 5),
            (r"\binterface file .* is (?:not|in)compatible\b", 5),
            (r"\bcompiled .* for a different version of agda\b", 4),
            (r"\bstdlib\b.*\b(mismatch|incompatible|version)\b", 3),
            (r"\bstandard library\b.*\b(incompatible|mismatch|version)\b", 3),
        ],
    ),
    (
        "missing module/import",
        [
            (r"\bcould not find module\b", 5),
            (r"\bcould not find interface file\b", 5),
            (r"\bcould not find (?:the )?source file\b", 4),
            (r"\bno such file or directory\b", 3),
            (r"\bfile '.*' was not found\b", 3),
            (r"\bnot in scope:.*\bimport\b", 2),
        ],
    ),
    (
        "unsolved meta",
        [
            (r"\bunsolved meta\b", 5),
            (r"\bunsolved metas?\b", 5),
            (r"\bfailed to solve (?:the )?following constraints\b", 4),
            (r"\bcannot solve constraint\b", 4),
            (r"\bmetavariable\b.*\bunsolved\b", 4),
        ],
    ),
    (
        "instance search/no candidate",
        [
            (r"\bcould not find (an|a) instance of the type\b", 5),
            (r"\bcould not find an instance\b", 5),
            (r"\bno instance of type\b", 5),
            (r"\bcannot find an instance\b", 4),
            (r"\bno instance found\b", 4),
            (r"\binstance search took too long\b", 4),
        ],
    ),
    (
        "termination",
        [
            (r"\btermination checking failed\b", 5),
            (r"\bnot accepted because termination\b", 5),
            (r"\bdoes not pass the termination check\b", 5),
            (r"\bnot structurally recursive\b", 4),
            (r"\btermination check\b.*\bfailed\b", 4),
        ],
    ),
    (
        "positivity",
        [
            (r"\bpositivity checking failed\b", 5),
            (r"\bpositivity has not been proven\b", 5),
            (r"\bcannot prove positivity\b", 4),
            (r"\bnot strictly positive\b", 4),
            (r"\bfailed to show positivity\b", 4),
        ],
    ),
    (
        "parse/scope error",
        [
            (r"\bparse error\b", 5),
            (r"\bparse of module\b.*\bfailed\b", 4),
            (r"\bunexpected token\b", 4),
            (r"\bsyntax error\b", 4),
            (r"\bnot in scope\b", 4),
            (r"\bunbound variable\b", 4),
            (r"\bunknown identifier\b", 4),
            (r"\bscope error\b", 5),
        ],
    ),
    (
        "type mismatch",
        [
            (r"\btype mismatch\b", 5),
            (r"\bWhen checking that the expression.*has type\b", 4),
            (r"\bexpression has type\b", 3),
            (r"\bgiven.*Expected:.*Found:\b", 4),
            (r"\bexpected.*but got\b", 3),
            (r"\btypes do not match\b", 5),
            (r"\bcould not infer type\b", 3),
        ],
    ),
]


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "logs",
        nargs="*",
        type=Path,
        help=(
            "Zero or more Agda log files to classify. Read from stdin when omitted "
            "or when '-' is used."
        ),
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="Emit JSON summary instead of plain text.",
    )
    return parser.parse_args(argv)


def read_inputs(paths: list[Path]) -> list[tuple[str, str]]:
    if not paths:
        return [("stdin", sys.stdin.read())]

    sources: list[tuple[str, str]] = []
    for path in paths:
        if str(path) == "-":
            sources.append(("stdin", sys.stdin.read()))
            continue

        try:
            sources.append((str(path), path.read_text(encoding="utf-8", errors="replace")))
        except OSError as exc:
            raise RuntimeError(f"failed to read {path}: {exc}") from exc
    return sources


def classify_text(text: str, source: str) -> tuple[dict[str, int], list[CategoryHit]]:
    scores: dict[str, int] = {category: 0 for category in FAILURE_CATEGORIES if category != "unknown"}
    hits: list[CategoryHit] = []

    for line_no, raw_line in enumerate(text.splitlines(), start=1):
        for category, pattern_weights in CATEGORY_PATTERNS:
            for pattern, weight in pattern_weights:
                if not re.search(pattern, raw_line, _CASE_INSENSITIVE):
                    continue
                scores[category] += weight
                hits.append(
                    CategoryHit(
                        category=category,
                        line_no=line_no,
                        source=source,
                        excerpt=raw_line.strip(),
                        score=weight,
                    )
                )

    return scores, hits


def merge_classification(
    all_scores: list[dict[str, int]],
) -> tuple[str, int, list[CategoryHit]]:
    totals: dict[str, int] = {category: 0 for category in FAILURE_CATEGORIES if category != "unknown"}
    for result in all_scores:
        for category, score in result.items():
            totals[category] += score

    ranked = sorted(
        (
            (category, score)
            for category, score in totals.items()
            if score > 0
        ),
        key=lambda pair: pair[1],
        reverse=True,
    )
    if not ranked:
        return "unknown", 0, []

    highest_score = ranked[0][1]
    top_categories = {pair[0] for pair in ranked if pair[1] == highest_score}
    if len(top_categories) == 1:
        return ranked[0][0], ranked[0][1], []

    # Tie-breaker by category order above; keep deterministic.
    category_priority = {c: i for i, c in enumerate(FAILURE_CATEGORIES)}
    winner = min(top_categories, key=lambda c: category_priority.get(c, 999))
    return winner, highest_score, []


def _conf(confidence_score: int, has_hits: bool, total_hits: int) -> str:
    if not has_hits:
        return "low"
    if confidence_score >= 12 or total_hits >= 4:
        return "high"
    if confidence_score >= 6 or total_hits >= 2:
        return "medium"
    return "low"


def summarize_hits(
    hits: list[CategoryHit],
) -> dict[str, dict[str, Any]]:
    grouped: dict[str, dict[str, Any]] = {}
    for hit in hits:
        bucket = grouped.setdefault(
            hit.category,
            {"count": 0, "examples": []},
        )
        bucket["count"] += 1
        if len(bucket["examples"]) < 3:
            bucket["examples"].append(
                {
                    "source": hit.source,
                    "line": hit.line_no,
                    "excerpt": hit.excerpt,
                }
            )
    return grouped


def print_text_report(
    likely: str,
    confidence: str,
    totals: dict[str, int],
    hits: list[CategoryHit],
    sources: list[str],
) -> None:
    grouped = summarize_hits(hits)
    print(f"Likely failure type: {likely}")
    print(f"Confidence: {confidence}")
    print(f"Sources: {', '.join(sources)}")
    if likely == "unknown":
        print("No strong Agda error pattern detected.")
        return

    print("Evidence:")
    for category in sorted(grouped):
        entry = grouped[category]
        score = totals.get(category, 0)
        print(f"- {category} (score {score}, {entry['count']} hits)")
        for ex in entry["examples"]:
            line = ex["line"]
            print(f"  - {ex['source']}:{line}: {ex['excerpt']}")


def build_json(
    likely: str,
    confidence: str,
    totals: dict[str, int],
    hits: list[CategoryHit],
    sources: list[str],
) -> dict[str, Any]:
    grouped = summarize_hits(hits)
    ranked = sorted(
        (
            {"category": category, "score": score, "examples": grouped[category]["examples"]}
            for category, score in totals.items()
            if score > 0
        ),
        key=lambda item: item["score"],
        reverse=True,
    )

    return {
        "likely_failure_type": likely,
        "confidence": confidence,
        "sources": sources,
        "scores": totals,
        "total_hits": len(hits),
        "matches": ranked,
    }


def main(argv: list[str] | None = None) -> int:
    args = parse_args(sys.argv[1:] if argv is None else argv)

    try:
        inputs = read_inputs(args.logs)
    except RuntimeError as exc:
        print(f"agda_failure_classifier: {exc}", file=sys.stderr)
        return 1

    all_hits: list[CategoryHit] = []
    all_scores: list[dict[str, int]] = []
    source_names: list[str] = []
    for source, text in inputs:
        source_names.append(source)
        scores, hits = classify_text(text, source)
        all_scores.append(scores)
        all_hits.extend(hits)

    totals = {category: 0 for category in FAILURE_CATEGORIES if category != "unknown"}
    for score in all_scores:
        for category, value in score.items():
            totals[category] += value

    likely, top_score, _ = merge_classification(all_scores)
    confidence = _conf(top_score, bool(all_hits), len(all_hits))

    if args.json:
        payload = build_json(likely, confidence, totals, all_hits, source_names)
        print(json.dumps(payload, indent=2))
        return 0

    print_text_report(likely, confidence, totals, all_hits, source_names)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
