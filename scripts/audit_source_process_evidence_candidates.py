#!/usr/bin/env python3
"""Discovery-only audit for source-process evidence migration candidates.

The script reads DASHI/**/*.agda and ranks files that match source-process
migration surfaces. It never rewrites Agda.
"""

from __future__ import annotations

import argparse
import json
import re
from dataclasses import dataclass, field
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
AGDA_ROOT = ROOT / "DASHI"
DEFAULT_OUTPUT_DIR = ROOT / "artifacts" / "source_process_evidence_audit"
DEFAULT_MD_OUT = DEFAULT_OUTPUT_DIR / "source_process_evidence_audit.md"
DEFAULT_JSON_OUT = DEFAULT_OUTPUT_DIR / "source_process_evidence_audit.json"


@dataclass
class PatternHit:
    kind: str
    count: int
    lines: list[int] = field(default_factory=list)
    examples: list[str] = field(default_factory=list)


@dataclass
class Candidate:
    file: str
    raw_score: int
    risk_score: int
    patterns: list[PatternHit]
    risk: str
    score: int
    summary: dict[str, int]


# Patterns aimed at source-process evidence and migration surfaces.
PATTERN_DEFS: tuple[tuple[str, re.Pattern[str], int, int], ...] = (
    (
        "source_process_evidence_phrase",
        re.compile(r"(?im)\bsource[-_\s]?process\b.*\bevidence\b|\bevidence.*\bsource[-_\s]?process\b"),
        10,
        -2,
    ),
    (
        "source_id",
        re.compile(r"(?im)\bsource[-_\s]?id\b|\bsourceId\b|\bsource id\b"),
        8,
        -1,
    ),
    (
        "generator_context",
        re.compile(r"(?im)\bsource\b.{0,40}\bgenerator\b|\bgenerator\b.{0,40}\bsource\b"),
        7,
        0,
    ),
    (
        "emission_context",
        re.compile(r"(?im)\bsource\b.{0,40}\bemission\b|\bemission\b.{0,40}\bsource\b|\bemitted\b.{0,40}\bsource\b"),
        7,
        0,
    ),
    (
        "batch_context",
        re.compile(r"(?im)\bsource\b.{0,40}\bbatch\b|\bbatch\b.{0,40}\bsource\b|\bpublic artifact batch\b"),
        6,
        0,
    ),
    (
        "trace_context",
        re.compile(r"(?im)\bsource\b.{0,40}\btrace\b|\btrace\b.{0,40}\bsource\b|\bobservable trace\b"),
        6,
        0,
    ),
    (
        "side_evidence",
        re.compile(r"(?im)\bside[-_\s]?evidence\b|\bside evidence\b"),
        9,
        0,
    ),
    (
        "source_fiber",
        re.compile(r"(?im)\bsource\s+fiber\b"),
        8,
        0,
    ),
    (
        "restricted_source_fiber",
        re.compile(r"(?im)\brestricted\s+source\s+fiber\b|\brestricted\s+fiber\b"),
        10,
        1,
    ),
    (
        "anomaly_context",
        re.compile(r"(?im)\bsource\b.{0,40}\banomaly\b|\banomaly\b.{0,40}\bsource\b|\banomaly\b.{0,60}\bsource process\b"),
        6,
        1,
    ),
    (
        "witness_context",
        re.compile(r"(?im)\bsource\b.{0,40}\bwitness\b|\bwitness\b.{0,40}\bsource\b|\brecovered witness\b"),
        7,
        1,
    ),
    (
        "source_compromise",
        re.compile(r"(?im)source[-_\s]?compromise|source\s+wide\s+compromise|sourceWideCompromise"),
        12,
        7,
    ),
)

# Surface-oriented patterns that indicate safer migration posture when present.
SAFETY_PATTERNS = (
    re.compile(r"(?im)\bcandidate[-_\s]?only\b|\bcandidate-only\b|\bcandidate only\b"),
    re.compile(r"(?im)\bnon[-_\s]?promot|\bpromoted\s+is\s+false\b|\bpromoted\b.*\bfalse\b"),
)

# Hardening patterns suggest this file may be a theorem/proof style surface or general code.
RISK_PATTERNS = (
    re.compile(r"(?im)\blemma\b|\bpostulate\b|\btheorem\b|\bproof\b"),
    re.compile(r"(?im)\bauthority|\bcausal\b|\bproduction\b|\bsecurity\b|\bclinical\b|\blegal\b|\btrading\b|\bgovernance\b"),
)


CORE_PREFIXES = (
    "DASHI/Core/",
    "DASHI/Interop/",
)

LOW_RISK_PREFIXES = (
    "DASHI/Core/",
    "DASHI/Execution/",
)
MEDIUM_RISK_PREFIXES = (
    "DASHI/Interop/",
    "DASHI/Promotion/",
)
HIGH_RISK_PREFIXES = (
    "DASHI/Crypto/",
)



def agda_files() -> list[Path]:
    return sorted(AGDA_ROOT.rglob("*.agda"))


def rel(path: Path) -> str:
    try:
        return path.relative_to(ROOT).as_posix()
    except ValueError:
        return path.as_posix()


def findall(pattern: re.Pattern[str], text: str) -> list[tuple[int, str]]:
    hits: list[tuple[int, str]] = []
    for match in pattern.finditer(text):
        span = text[: match.start()].count("\n") + 1
        snippet = match.group(0).replace("\n", " ").strip()
        if len(snippet) > 100:
            snippet = snippet[:97] + "..."
        hits.append((span, snippet))
    return hits


def classify(path: Path, text: str) -> Candidate | None:
    pattern_hits: list[PatternHit] = []
    total = 0
    risk_count = 0
    matched = False

    for name, pattern, weight, risk_delta in PATTERN_DEFS:
        matches = findall(pattern, text)
        if not matches:
            continue
        matched = True
        count = len(matches)
        total += weight * count
        risk_count += risk_delta * count
        lines = [line for line, _ in matches[:4]]
        examples = [snippet for _, snippet in matches[:2]]
        pattern_hits.append(PatternHit(name, count, lines, examples))

    if not matched:
        return None

    # Safe-candidate adjustment: explicit candidate/non-promoting language reduces risk.
    safe_bonus = sum(1 for pattern in SAFETY_PATTERNS if pattern.search(text))
    hard_risk_penalty = sum(1 for pattern in RISK_PATTERNS if pattern.search(text))

    risk_count = risk_count - safe_bonus + hard_risk_penalty

    risk = classify_risk(rel(path), total, risk_count)
    score = total

    summary = {
        "patterns": sum(hit.count for hit in pattern_hits),
        "source_fiber_mentions": next(
            (hit.count for hit in pattern_hits if hit.kind in ("source_fiber", "restricted_source_fiber")),
            0,
        ),
        "compromise_mentions": next(
            (hit.count for hit in pattern_hits if hit.kind == "source_compromise"),
            0,
        ),
    }

    return Candidate(
        file=rel(path),
        raw_score=total,
        risk_score=risk_count,
        patterns=pattern_hits,
        risk=risk,
        score=score,
        summary=summary,
    )


def classify_risk(file_text: str, raw_score: int, risk_count: int) -> str:
    if any(file_text.startswith(prefix) for prefix in CORE_PREFIXES):
        risk_count -= 2

    if any(file_text.startswith(prefix) for prefix in LOW_RISK_PREFIXES):
        risk_count -= 2
    elif any(file_text.startswith(prefix) for prefix in MEDIUM_RISK_PREFIXES):
        risk_count += 1
    elif any(file_text.startswith(prefix) for prefix in HIGH_RISK_PREFIXES):
        risk_count += 3

    if raw_score >= 80 and risk_count <= 1:
        return "low"
    if risk_count >= 7:
        return "high"
    if risk_count >= 3:
        return "medium"
    return "low"


def risk_rank(risk: str) -> int:
    return {"low": 0, "medium": 1, "high": 2}[risk]


def candidate_sort_key(candidate: Candidate) -> tuple[int, int, str]:
    return (risk_rank(candidate.risk), -candidate.score, candidate.file)


def as_jsonable(candidate: Candidate) -> dict[str, object]:
    return {
        "file": candidate.file,
        "score": candidate.score,
        "risk": candidate.risk,
        "risk_score": candidate.risk_score,
        "summary": candidate.summary,
        "patterns": [
            {
                "kind": hit.kind,
                "count": hit.count,
                "lines": hit.lines,
                "examples": hit.examples,
            }
            for hit in candidate.patterns
        ],
    }


def render_markdown(candidates: list[Candidate], limit: int) -> str:
    risk_counts = {
        "low": sum(1 for candidate in candidates if candidate.risk == "low"),
        "medium": sum(1 for candidate in candidates if candidate.risk == "medium"),
        "high": sum(1 for candidate in candidates if candidate.risk == "high"),
    }
    total_matches = sum(candidate.summary["patterns"] for candidate in candidates)

    lines = [
        "# Source-Process Evidence Migration Candidate Audit",
        "",
        "Discovery-only scan. This script reports candidates and risk tiers only; it does not edit Agda.",
        "",
        "## Summary",
        f"- Scanned files: {len(agda_files())}",
        f"- Total candidates: {len(candidates)}",
        f"- Matched pattern hits: {total_matches}",
        f"- Low-risk: {risk_counts['low']}",
        f"- Medium-risk: {risk_counts['medium']}",
        f"- High-risk: {risk_counts['high']}",
        "",
        "## Ranked Candidates",
        f"(Sorted by risk then score, limited to {limit} entries in this section)",
    ]

    for candidate in candidates[:limit]:
        lines.extend(
            [
                "",
                f"### {candidate.file}",
                f"- Risk: `{candidate.risk}`",
                f"- Score: `{candidate.score}`",
                f"- Risk score: `{candidate.risk_score}`",
                f"- Pattern hits: `{candidate.summary['patterns']}`",
                f"- Source-fiber hits: `{candidate.summary['source_fiber_mentions']}`",
                f"- Source-compromise hits: `{candidate.summary['compromise_mentions']}`",
                "",
                "- Pattern details:",
            ]
        )
        for hit in candidate.patterns:
            sample = ", ".join(f"{hit.count}@{line}" for line in hit.lines[:3]) if hit.lines else "(line unknown)"
            if len(sample) > 140:
                sample = sample[:137] + "..."
            lines.append(f"  - `{hit.kind}` ({hit.count}): {sample}")

    if not candidates:
        lines.extend(["", "No files matched the source-process evidence migration patterns."])

    lines.extend(
        [
            "",
            "## Notes",
            "",
            "- This is a discovery-only report and intentionally does not emit edits.",
            "- "
            "Files near `source-process evidence` vocabulary and source-process source-fiber/witness/compromise interfaces are ranked highest.",
            "- Inspect high-risk files manually before any migration or refactor decisions.",
        ]
    )

    return "\n".join(lines)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Audit source-process evidence candidates.")
    parser.add_argument("--repo-root", type=Path, default=ROOT)
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=None,
        help="Output directory for --write (defaults to artifacts/source_process_evidence_audit under --repo-root).",
    )
    parser.add_argument("--md-out", type=Path, default=None)
    parser.add_argument("--json-out", type=Path, default=None)
    parser.add_argument("--write", action="store_true", help="Write markdown report under artifacts by default.")
    parser.add_argument("--write-json", action="store_true", help="Also write JSON report when --write is enabled.")
    parser.add_argument("--limit", type=int, default=150, help="Max candidates shown in markdown section")
    return parser.parse_args()


def write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def write_json(path: Path, payload: dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def display_path(path: Path) -> str:
    try:
        return path.relative_to(ROOT).as_posix()
    except ValueError:
        return path.as_posix()


def main() -> int:
    args = parse_args()

    # Keep repository-root aware if caller supplies an explicit project root.
    global ROOT, AGDA_ROOT, DEFAULT_OUTPUT_DIR, DEFAULT_MD_OUT, DEFAULT_JSON_OUT
    ROOT = args.repo_root.resolve()
    AGDA_ROOT = ROOT / "DASHI"
    DEFAULT_OUTPUT_DIR = Path(args.output_dir or (ROOT / "artifacts" / "source_process_evidence_audit"))
    DEFAULT_MD_OUT = DEFAULT_OUTPUT_DIR / "source_process_evidence_audit.md"
    DEFAULT_JSON_OUT = DEFAULT_OUTPUT_DIR / "source_process_evidence_audit.json"

    candidates = [
        candidate
        for path in agda_files()
        if (candidate := classify(path, path.read_text(encoding="utf-8"))) is not None
    ]
    candidates.sort(key=candidate_sort_key)

    if args.limit <= 0:
        args.limit = len(candidates)

    markdown = render_markdown(candidates, args.limit)
    print(markdown)

    if args.write:
        md_out = args.md_out or DEFAULT_MD_OUT
        write_text(md_out, markdown)

        if args.write_json:
            summary = {
                "total_candidates": len(candidates),
                "low_risk": sum(1 for candidate in candidates if candidate.risk == "low"),
                "medium_risk": sum(1 for candidate in candidates if candidate.risk == "medium"),
                "high_risk": sum(1 for candidate in candidates if candidate.risk == "high"),
                "total_pattern_hits": sum(candidate.summary["patterns"] for candidate in candidates),
            }
            json_out = args.json_out or DEFAULT_JSON_OUT
            json_payload = {
                "summary": summary,
                "candidates": [as_jsonable(candidate) for candidate in candidates],
            }
            write_json(json_out, json_payload)
            print()
            print(f"Wrote {display_path(md_out)}")
            print(f"Wrote {display_path(json_out)}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
