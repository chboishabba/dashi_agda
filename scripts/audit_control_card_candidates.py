#!/usr/bin/env python3
"""Audit repeated ORCSLPGF/control-card candidates.

This is a discovery-only scanner. It reads Agda sources, ranks files that
repeat O/R/C/S/L/P/G/F or ORCSLPGF surfaces, and never rewrites code.
"""

from __future__ import annotations

import argparse
import json
import re
from dataclasses import dataclass, field
from pathlib import Path
from typing import Iterable


ROOT = Path(__file__).resolve().parents[1]
AGDA_ROOT = ROOT / "DASHI"
DEFAULT_OUTPUT_DIR = ROOT / "artifacts" / "control_card_audit"
DEFAULT_JSON_OUT = DEFAULT_OUTPUT_DIR / "control_card_audit.json"
DEFAULT_MD_OUT = DEFAULT_OUTPUT_DIR / "control_card_audit.md"


RECORD_DECL_RE = re.compile(
    r"(?m)^\s*record\s+([A-Za-z][A-Za-z0-9']*)\s*(?:\{[^}]*\}\s*)?"
    r"(?:\([^)]*\)\s*)*:\s*Set(?:ω|₁|₂|₃|\d)?"
)

FIELD_DECL_RE = re.compile(r"(?m)^\s{2,}([A-Za-z][A-Za-z0-9']*)\s*:\s*([^\n]+)$")

CANONICAL_DECL_RE = re.compile(
    r"(?m)^\s*canonical([A-Za-z][A-Za-z0-9']*(?:ORCSLPGF|ControlCard)[A-Za-z0-9']*)\s*:\s*"
)

CANONICAL_ASSIGN_RE = re.compile(
    r"(?m)^\s*canonical([A-Za-z][A-Za-z0-9']*(?:ORCSLPGF|ControlCard)[A-Za-z0-9']*)\s*="
)

DEDICATED_RECORD_RE = re.compile(
    r"(?m)^\s*record\s+([A-Za-z][A-Za-z0-9']*(?:ORCSLPGF|ControlCard)[A-Za-z0-9']*)\s*:\s*Set"
)

LETTER_FIELD_RE = re.compile(r"(?m)^\s{2,}([ORCSLPGF])\s*:\s*(String|Bool|Nat|List\s+String)\b")

LEDGER_TOKEN_RE = re.compile(r"\bO/R/C/S/L/P/G/F\b")
ORCSLPGF_TOKEN_RE = re.compile(r"\bORCSLPGF\b")
CONTROL_CARD_TOKEN_RE = re.compile(r"\bControlCard\b|\bcontrol[- ]card\b|\bcontrol_card\b", re.I)
CANONICAL_EQUALITY_RE = re.compile(
    r"(?m)^\s*[A-Za-z][A-Za-z0-9'._]*\s*≡\s*canonical[A-Za-z][A-Za-z0-9']*(?:ORCSLPGF|ControlCard)[A-Za-z0-9']*\b"
)
ORCSLPGF_ROW_RE = re.compile(r"\bORCSLPGFRow\b|\bORCSLPGFRows\b|\bORCSLPGFSummary\b")
CONTROL_CARD_ROW_RE = re.compile(r"\bControlCardStrings\b|\bControlCard\b")

LOW_RISK_PREFIXES = (
    "DASHI/Physics/Closure/",
    "DASHI/Physics/ClosureGlue/",
)

MEDIUM_RISK_PREFIXES = (
    "DASHI/Physics/",
    "DASHI/Algebra/",
)

AVOID_TOKENS = (
    "Theorem",
    "Lemma",
    "Proof",
    "Instance",
    "Regression",
    "Everything",
    "Examples",
)


@dataclass
class PatternHit:
    kind: str
    names: list[str] = field(default_factory=list)
    count: int = 0
    note: str = ""


@dataclass
class Candidate:
    file: str
    risk: str
    score: int
    raw_score: int
    patterns: list[PatternHit]
    notes: list[str]
    summary: dict[str, int]


def agda_files() -> list[Path]:
    return sorted(AGDA_ROOT.rglob("*.agda"))


def rel(path: Path) -> str:
    return path.relative_to(ROOT).as_posix()


def unique(items: Iterable[str], limit: int = 12) -> list[str]:
    out: list[str] = []
    seen: set[str] = set()
    for item in items:
        if item in seen or not item:
            continue
        seen.add(item)
        out.append(item)
        if len(out) >= limit:
            break
    return out


def findall(pattern: re.Pattern[str], text: str) -> list[str]:
    matches = pattern.findall(text)
    out: list[str] = []
    for match in matches:
        if isinstance(match, tuple):
            out.append(next((part for part in match if part), ""))
        else:
            out.append(match)
    return [item for item in out if item]


def score_summary(patterns: list[PatternHit]) -> dict[str, int]:
    summary = {key: 0 for key in "ORCSLPGF"}
    for hit in patterns:
        if hit.kind == "letter_fields":
            for name in hit.names:
                if name in summary:
                    summary[name] += hit.count
        elif hit.kind in {"dedicated_record", "canonical_decl", "canonical_assign", "canonical_equality", "row_surface", "control_card_surface", "ledger_token"}:
            for key in summary:
                summary[key] += 1
    return summary


def classify_patterns(text: str) -> list[PatternHit]:
    hits: list[PatternHit] = []

    dedicated_records = unique(findall(DEDICATED_RECORD_RE, text))
    if dedicated_records:
        hits.append(
            PatternHit(
                kind="dedicated_record",
                names=dedicated_records,
                count=len(dedicated_records),
                note="record name encodes ORCSLPGF/control-card surface",
            )
        )

    canonical_decls = unique(findall(CANONICAL_DECL_RE, text))
    if canonical_decls:
        hits.append(
            PatternHit(
                kind="canonical_decl",
                names=canonical_decls,
                count=len(canonical_decls),
                note="canonical binding with ORCSLPGF/control-card name",
            )
        )

    canonical_assigns = unique(findall(CANONICAL_ASSIGN_RE, text))
    if canonical_assigns:
        hits.append(
            PatternHit(
                kind="canonical_assign",
                names=canonical_assigns,
                count=len(canonical_assigns),
                note="canonical value assignment",
            )
        )

    letter_fields = unique(findall(LETTER_FIELD_RE, text))
    if letter_fields:
        hits.append(
            PatternHit(
                kind="letter_fields",
                names=letter_fields,
                count=len(letter_fields),
                note="explicit O/R/C/S/L/P/G/F field block",
            )
        )

    equality_locks = unique(findall(CANONICAL_EQUALITY_RE, text))
    if equality_locks:
        hits.append(
            PatternHit(
                kind="canonical_equality",
                names=equality_locks,
                count=len(equality_locks),
                note="field locked to canonical ORCSLPGF/control-card value",
            )
        )

    row_surface = unique(findall(ORCSLPGF_ROW_RE, text))
    if row_surface:
        hits.append(
            PatternHit(
                kind="row_surface",
                names=row_surface,
                count=len(row_surface),
                note="row or summary surface for O/R/C/S/L/P/G/F",
            )
        )

    control_card_surface = unique(findall(CONTROL_CARD_TOKEN_RE, text))
    if control_card_surface:
        hits.append(
            PatternHit(
                kind="control_card_surface",
                names=control_card_surface,
                count=len(control_card_surface),
                note="control-card wording or identifier surface",
            )
        )

    ledger_tokens = unique(findall(LEDGER_TOKEN_RE, text))
    if ledger_tokens:
        hits.append(
            PatternHit(
                kind="ledger_token",
                names=ledger_tokens,
                count=len(ledger_tokens),
                note="literal O/R/C/S/L/P/G/F ledger text",
            )
        )

    if not hits:
        return []

    record_names = unique(findall(RECORD_DECL_RE, text))
    if record_names:
        hits.insert(
            0,
            PatternHit(
                kind="record_surface",
                names=record_names,
                count=len(record_names),
                note="record declaration in the same file",
            ),
        )

    return hits


def raw_score(patterns: list[PatternHit]) -> int:
    weights = {
        "record_surface": 3,
        "dedicated_record": 8,
        "canonical_decl": 6,
        "canonical_assign": 4,
        "letter_fields": 5,
        "canonical_equality": 4,
        "row_surface": 3,
        "control_card_surface": 3,
        "ledger_token": 2,
    }
    return sum(weights[hit.kind] * max(1, hit.count) for hit in patterns)


def risk_and_notes(path: Path, text: str, score: int, patterns: list[PatternHit]) -> tuple[str, int, list[str]]:
    path_text = rel(path)
    notes: list[str] = []
    adjusted = score

    if path_text.startswith(LOW_RISK_PREFIXES):
        adjusted += 4
        notes.append("closure/receipt namespace")
    elif path_text.startswith(MEDIUM_RISK_PREFIXES):
        adjusted += 1
        notes.append("physics/algebra namespace")
    else:
        adjusted -= 2
        notes.append("non-closure namespace")

    if any(token in path_text for token in AVOID_TOKENS):
        adjusted -= 6
        notes.append("avoid by policy: theorem/proof-style module")

    if "ControlCard" in text and "canonicalControlCard" in text:
        adjusted += 4
        notes.append("full control-card surface present")

    if "ORCSLPGF" in text and "canonical" in text:
        adjusted += 4
        notes.append("full ORCSLPGF surface present")

    if "record ControlCard" in text or "record " in text and "ORCSLPGF" in text:
        adjusted += 2

    if "O =" in text and "R =" in text and "C =" in text:
        adjusted += 2

    if "orcslpgf" in text.lower() and "canonical" in text.lower():
        adjusted += 2

    if "canonicalORCSLPGFSummary" in text or "canonicalControlCardStrings" in text:
        adjusted += 2
        notes.append("summary/list surface present")

    if any(hit.kind == "letter_fields" for hit in patterns):
        notes.append("explicit O/R/C/S/L/P/G/F fields found")
    if any(hit.kind == "dedicated_record" for hit in patterns):
        notes.append("dedicated record name found")

    if adjusted >= 18 and path_text.startswith(LOW_RISK_PREFIXES):
        risk = "low"
    elif adjusted >= 10:
        risk = "medium"
    else:
        risk = "avoid"

    if risk == "low":
        notes.append("likely migration-safe if public names stay stable")
    elif risk == "medium":
        notes.append("review for exact surface and constructor naming")
    else:
        notes.append("defer unless this file is the explicit target")

    return risk, adjusted, unique(notes, limit=16)


def candidate_for(path: Path) -> Candidate | None:
    text = path.read_text(encoding="utf-8")
    patterns = classify_patterns(text)
    if not patterns:
        return None

    base = raw_score(patterns)
    risk, score, notes = risk_and_notes(path, text, base, patterns)
    summary = score_summary(patterns)
    return Candidate(
        file=rel(path),
        risk=risk,
        score=score,
        raw_score=base,
        patterns=patterns,
        notes=notes,
        summary=summary,
    )


def candidate_sort_key(candidate: Candidate) -> tuple[int, int, int, str]:
    risk_rank = {"low": 0, "medium": 1, "avoid": 2}[candidate.risk]
    dedicated_rank = 0 if any(hit.kind == "dedicated_record" for hit in candidate.patterns) else 1
    return (dedicated_rank, risk_rank, -candidate.score, candidate.file)


def as_jsonable(candidate: Candidate) -> dict[str, object]:
    return {
        "file": candidate.file,
        "risk": candidate.risk,
        "score": candidate.score,
        "raw_score": candidate.raw_score,
        "summary": candidate.summary,
        "patterns": [
            {
                "kind": pattern.kind,
                "names": pattern.names,
                "count": pattern.count,
                "note": pattern.note,
            }
            for pattern in candidate.patterns
        ],
        "notes": candidate.notes,
    }


def render_markdown(candidates: list[Candidate], limit: int) -> str:
    risk_counts = {
        risk: sum(1 for candidate in candidates if candidate.risk == risk)
        for risk in ("low", "medium", "avoid")
    }
    summary = {key: 0 for key in "ORCSLPGF"}
    for candidate in candidates:
        for key, value in candidate.summary.items():
            summary[key] += value

    lines = [
        "# ORCSLPGF Control-Card Candidate Audit",
        "",
        "Discovery-only report. Do not rewrite Agda; review candidate files by hand.",
        "",
        "## Summary",
        "",
        f"- Total candidates: {len(candidates)}",
        f"- Low risk: {risk_counts['low']}",
        f"- Medium risk: {risk_counts['medium']}",
        f"- Avoid/defer: {risk_counts['avoid']}",
        "",
        "## O/R/C/S/L/P/G/F",
        "",
        *[f"- {key}: {summary[key]}" for key in "ORCSLPGF"],
        "",
        "## Top Ranked Candidates",
        "",
    ]

    for candidate in candidates[:limit]:
        pattern_labels = ", ".join(pattern.kind for pattern in candidate.patterns)
        notes = "; ".join(candidate.notes)
        lines.extend(
            [
                f"### {candidate.file}",
                "",
                f"- Risk: `{candidate.risk}`",
                f"- Score: `{candidate.score}` (raw `{candidate.raw_score}`)",
                f"- Patterns: {pattern_labels}",
                f"- Notes: {notes}",
                "",
            ]
        )
        for pattern in candidate.patterns:
            names = ", ".join(pattern.names[:10])
            suffix = "" if len(pattern.names) <= 10 else " ..."
            lines.append(f"  - `{pattern.kind}` ({pattern.count}): {names}{suffix}")
        lines.append("")

    lines.extend(
        [
            "## Policy",
            "",
            "- Prefer full control-card modules with canonical bindings and stable public names.",
            "- Treat partial mentions, summary-only strings, and external consumers as review items.",
            "- Defer theorem/proof-style modules unless they are the explicit target surface.",
            "",
        ]
    )
    return "\n".join(lines)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Rank Agda ORCSLPGF/control-card candidates."
    )
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=DEFAULT_OUTPUT_DIR,
        help="Directory for default JSON/Markdown reports.",
    )
    parser.add_argument(
        "--json-out",
        type=Path,
        default=None,
        help="Write JSON report to this path. Defaults to <output-dir>/control_card_audit.json.",
    )
    parser.add_argument(
        "--md-out",
        type=Path,
        default=None,
        help="Write Markdown report to this path. Defaults to <output-dir>/control_card_audit.md.",
    )
    parser.add_argument(
        "--limit",
        type=int,
        default=80,
        help="Maximum candidates to include in the Markdown detail section.",
    )
    parser.add_argument(
        "--no-write",
        action="store_true",
        help="Print summary only; do not write report files.",
    )
    return parser.parse_args()


def write_json(path: Path, payload: dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")


def display_path(path: Path) -> str:
    try:
        return path.relative_to(ROOT).as_posix()
    except ValueError:
        return path.as_posix()


def main() -> int:
    args = parse_args()
    json_out = args.json_out or DEFAULT_JSON_OUT
    md_out = args.md_out or DEFAULT_MD_OUT

    candidates = [
        candidate
        for path in agda_files()
        if (candidate := candidate_for(path)) is not None
    ]
    candidates.sort(key=candidate_sort_key)

    risk_counts = {
        risk: sum(1 for candidate in candidates if candidate.risk == risk)
        for risk in ("low", "medium", "avoid")
    }
    summary = {key: 0 for key in "ORCSLPGF"}
    for candidate in candidates:
        for key, value in candidate.summary.items():
            summary[key] += value

    print("ORCSLPGF/control-card candidate audit")
    print("=====================================")
    print(f"Scanned Agda files: {len(agda_files())}")
    print(f"Total candidates: {len(candidates)}")
    print(f"Low risk: {risk_counts['low']}")
    print(f"Medium risk: {risk_counts['medium']}")
    print(f"Avoid/defer: {risk_counts['avoid']}")
    print("O/R/C/S/L/P/G/F:")
    for key in "ORCSLPGF":
        print(f"  {key}: {summary[key]}")
    print()
    print("Top low-risk candidates:")
    low_candidates = [candidate for candidate in candidates if candidate.risk == "low"]
    for candidate in low_candidates[:12]:
        print(f"  - {candidate.file} (score {candidate.score})")

    if not args.no_write:
        payload = {
            "summary": {
                "total": len(candidates),
                "low": risk_counts["low"],
                "medium": risk_counts["medium"],
                "avoid": risk_counts["avoid"],
                "orcslpgf": summary,
            },
            "candidates": [as_jsonable(candidate) for candidate in candidates],
        }
        write_json(json_out, payload)
        md_out.parent.mkdir(parents=True, exist_ok=True)
        md_out.write_text(render_markdown(candidates, args.limit), encoding="utf-8")
        print()
        print(f"Wrote {display_path(json_out)}")
        print(f"Wrote {display_path(md_out)}")

    print()
    print("Deferred by policy: theorem/proof-heavy modules, partial mentions, and external consumers.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
