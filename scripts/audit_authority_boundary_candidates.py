#!/usr/bin/env python3
"""Audit authority-boundary migration candidates.

This is a discovery/ranking tool only.  It intentionally does not rewrite
Agda: authority-boundary migrations still need local proof review because
small naming and universe changes can affect typechecking.
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
DEFAULT_OUTPUT_DIR = ROOT / "artifacts" / "authority_boundary_audit"


AUTHORITY_NAME_RE = re.compile(
    r"\b([A-Za-z][A-Za-z0-9']*(?:Authority|AuthorityClaim|AuthorityBoundary)"
    r"[A-Za-z0-9']*)\b"
)

FIELD_DECL_RE = re.compile(
    r"(?m)^\s{2,}([A-Za-z][A-Za-z0-9']*)\s*:\s*(?:Bool|.*Authority.*|.*Boundary.*)$"
)

FALSE_PROOF_RE = re.compile(
    r"(?m)^\s*([A-Za-z][A-Za-z0-9']*(?:IsFalse|False|Blocked|NotPromoted|"
    r"NoAuthority|Authority.*False)[A-Za-z0-9']*)\s*:\s*"
    r"[^\n]*(?:Authority|Promot|Claim|Clinical|Theorem|Clay|Terminal|"
    r"Runtime|Legal|Trading|Metaphysical|Spiritual|Empirical|Support|"
    r"Admissibility)[^\n]*≡\s*false\b"
)

TRUE_BLOCK_RE = re.compile(
    r"(?m)^\s*([A-Za-z][A-Za-z0-9']*(?:Blocked|Boundary|NotSupplied|"
    r"Required|StillOpen)[A-Za-z0-9']*)\s*:\s*[^\n]*≡\s*true\b"
)

EMPTY_PROMOTION_RE = re.compile(
    r"(?ms)^data\s+([A-Za-z][A-Za-z0-9']*(?:Promotion|Authority|Claim)"
    r"[A-Za-z0-9']*)\s*:\s*Set(?:ω|₁|₂|₃)?\s+where\s*(?:\n\s*){0,3}"
    r"(?=^[A-Za-z]|^record|^data|^module|^open|^import|\Z)"
)

CANDIDATE_ONLY_RE = re.compile(
    r"(?ms)\bcandidateOnly\s*:\s*Bool\b.*?\bcandidateOnlyIsTrue\s*:"
)

PROMOTED_FALSE_RE = re.compile(
    r"(?ms)\b([A-Za-z][A-Za-z0-9']*(?:promoted|Promoted|promotion|Promotion)"
    r"[A-Za-z0-9']*)\s*:\s*Bool\b.*?\b\1[A-Za-z0-9']*IsFalse\s*:"
)

BLOCKED_CLAIM_RE = re.compile(
    r"(?ms)^data\s+([A-Za-z][A-Za-z0-9']*(?:Blocked|Boundary|Claim|Authority)"
    r"[A-Za-z0-9']*)\s*:\s*Set(?:ω|₁|₂|₃)?\s+where.*?"
    r"\bcanonical[A-Za-z0-9']*(?:Blocked|Boundary|Claim|Authority)[A-Za-z0-9']*"
)

ADAPTER_CANONICALITY_RE = re.compile(
    r"(?ms)\b([A-Za-z][A-Za-z0-9']*(?:Adapter|Core|Receipt))\s*:\s*"
    r"[^\n]+?\n.*?\b\1IsCanonical\s*:"
)

BRIDGE_REQUIRED_RE = re.compile(
    r"(?ms)\b([A-Za-z][A-Za-z0-9']*(?:bridge|Bridge)[A-Za-z0-9']*)\s*:\s*"
    r"Bool\b.*?\b\1[A-Za-z0-9']*(?:IsFalse|IsTrue|Required|Supplied)\s*:"
)

WITH_ABSTRACTION_RE = re.compile(r"(?m)(?:^\s*with\s+|\bwith\s+)")
PATTERN_MATCH_RE = re.compile(r"(?m)^\s*[A-Za-z_][A-Za-z0-9'_]*\s+.+?=")


LOW_RISK_PREFIXES = (
    "DASHI/Interop/",
    "DASHI/Promotion/",
    "DASHI/Biology/",
    "DASHI/Culture/",
    "DASHI/Ontology/",
)

HIGH_RISK_PREFIXES = (
    "DASHI/Physics/Closure/",
    "DASHI/Cubical/",
    "DASHI/Quantum/",
)

AVOID_TOKENS = (
    "GR",
    "NS",
    "YM",
    "YangMills",
    "Navier",
    "Einstein",
    "Ricci",
    "Schwarzschild",
    "Continuum",
    "Clay",
)

THEOREMISH_TOKENS = (
    "Theorem",
    "Lemma",
    "Sound",
    "Complete",
    "Continuum",
    "Convergence",
    "Compactness",
    "SelfAdjoint",
    "Generator",
)


@dataclass
class PatternHit:
    kind: str
    names: list[str] = field(default_factory=list)
    count: int = 0
    suggested_cores: list[str] = field(default_factory=list)


@dataclass
class Candidate:
    file: str
    risk: str
    score: int
    raw_score: int
    patterns: list[PatternHit]
    suggested_cores: list[str]
    notes: list[str]


def agda_files() -> list[Path]:
    return sorted(AGDA_ROOT.rglob("*.agda"))


def rel(path: Path) -> str:
    return path.relative_to(ROOT).as_posix()


def unique(items: Iterable[str], limit: int = 12) -> list[str]:
    out: list[str] = []
    seen: set[str] = set()
    for item in items:
        if item in seen:
            continue
        seen.add(item)
        out.append(item)
        if len(out) >= limit:
            break
    return out


def findall(pattern: re.Pattern[str], text: str) -> list[str]:
    matches = pattern.findall(text)
    names: list[str] = []
    for match in matches:
        if isinstance(match, tuple):
            names.append(next((part for part in match if part), ""))
        else:
            names.append(match)
    return [name for name in names if name]


def classify_patterns(text: str) -> list[PatternHit]:
    hits: list[PatternHit] = []

    authority_names = [
        name
        for name in findall(AUTHORITY_NAME_RE, text)
        if not name.startswith("canonical")
    ]
    field_names = findall(FIELD_DECL_RE, text)
    authority_field_names = [
        name for name in field_names if "Authority" in name or "Boundary" in name
    ]
    authority_cluster = unique(authority_field_names + authority_names)
    if len(authority_cluster) >= 3:
        hits.append(
            PatternHit(
                kind="authority_field_cluster",
                names=authority_cluster,
                count=len(authority_field_names) or len(authority_cluster),
                suggested_cores=[
                    "AuthorityBoundaryCore",
                    "AuthorityNonPromotionCore",
                ],
            )
        )

    false_proofs = unique(findall(FALSE_PROOF_RE, text))
    if false_proofs:
        hits.append(
            PatternHit(
                kind="false_authority_bool",
                names=false_proofs,
                count=len(findall(FALSE_PROOF_RE, text)),
                suggested_cores=[
                    "AuthorityNonPromotionCore",
                    "AuthorityBoundaryCore",
                ],
            )
        )

    true_blocks = unique(findall(TRUE_BLOCK_RE, text))
    if true_blocks:
        hits.append(
            PatternHit(
                kind="true_block_or_boundary_flag",
                names=true_blocks,
                count=len(findall(TRUE_BLOCK_RE, text)),
                suggested_cores=[
                    "AuthorityBoundaryCore",
                    "BridgeRequirementCore",
                ],
            )
        )

    empty_promotions = unique(findall(EMPTY_PROMOTION_RE, text))
    if empty_promotions:
        hits.append(
            PatternHit(
                kind="empty_promotion_datatype",
                names=empty_promotions,
                count=len(findall(EMPTY_PROMOTION_RE, text)),
                suggested_cores=["EmptyPromotionCore"],
            )
        )

    if CANDIDATE_ONLY_RE.search(text) or PROMOTED_FALSE_RE.search(text):
        names = []
        if CANDIDATE_ONLY_RE.search(text):
            names.append("candidateOnly/candidateOnlyIsTrue")
        names.extend(unique(findall(PROMOTED_FALSE_RE, text), limit=8))
        hits.append(
            PatternHit(
                kind="candidate_only_promoted_false_bundle",
                names=names,
                count=len(names),
                suggested_cores=["CandidateOnlyCore", "AuthorityNonPromotionCore"],
            )
        )

    blocked_vocab = unique(findall(BLOCKED_CLAIM_RE, text))
    if blocked_vocab:
        hits.append(
            PatternHit(
                kind="blocked_claim_vocabulary",
                names=blocked_vocab,
                count=len(findall(BLOCKED_CLAIM_RE, text)),
                suggested_cores=["AuthorityBoundaryCore"],
            )
        )

    adapter_pairs = unique(findall(ADAPTER_CANONICALITY_RE, text))
    if adapter_pairs:
        hits.append(
            PatternHit(
                kind="adapter_canonicality_pair",
                names=adapter_pairs,
                count=len(findall(ADAPTER_CANONICALITY_RE, text)),
                suggested_cores=["AdapterCanonicalityCore"],
            )
        )

    bridge_pairs = unique(findall(BRIDGE_REQUIRED_RE, text))
    if bridge_pairs:
        hits.append(
            PatternHit(
                kind="bridge_required_or_supplied_bundle",
                names=bridge_pairs,
                count=len(findall(BRIDGE_REQUIRED_RE, text)),
                suggested_cores=["BridgeRequirementCore"],
            )
        )

    return hits


def raw_score(patterns: list[PatternHit]) -> int:
    weights = {
        "authority_field_cluster": 5,
        "false_authority_bool": 4,
        "true_block_or_boundary_flag": 2,
        "empty_promotion_datatype": 4,
        "candidate_only_promoted_false_bundle": 3,
        "blocked_claim_vocabulary": 3,
        "adapter_canonicality_pair": 2,
        "bridge_required_or_supplied_bundle": 3,
    }
    return sum(weights[hit.kind] * max(1, hit.count) for hit in patterns)


def risk_and_notes(path: Path, text: str, score: int) -> tuple[str, int, list[str]]:
    path_text = rel(path)
    notes: list[str] = []
    adjusted = score

    if path_text.startswith(LOW_RISK_PREFIXES):
        adjusted += 2
        notes.append("receipt-surface namespace")
    if path_text.startswith(HIGH_RISK_PREFIXES):
        adjusted -= 8
        notes.append("physics/analytic namespace")

    basename = path.name
    if any(token in path_text for token in AVOID_TOKENS):
        adjusted -= 8
        notes.append("avoid by policy: GR/NS/YM/Clay-adjacent name")

    theoremish_count = sum(text.count(token) for token in THEOREMISH_TOKENS)
    if theoremish_count >= 8:
        adjusted -= 5
        notes.append("theorem-heavy vocabulary")

    pattern_match_count = len(PATTERN_MATCH_RE.findall(text))
    with_count = len(WITH_ABSTRACTION_RE.findall(text))
    if with_count:
        adjusted -= min(6, with_count)
        notes.append("contains with-abstractions")
    if pattern_match_count >= 80:
        adjusted -= 4
        notes.append("many pattern-matching clauses")

    if "Setω" in text:
        adjusted -= 2
        notes.append("universe-polymorphic/Setω surface")

    if "DASHI.Promotion.AuthorityBoundaryCore" in text:
        adjusted -= 35
        notes.append("already consumes AuthorityBoundaryCore")
    if "DASHI.Biology.BioactiveAuthorityBoundaryCore" in text:
        adjusted -= 20
        notes.append("already consumes BioactiveAuthorityBoundaryCore")

    if any(token in basename for token in ("Boundary", "Bridge", "Receipt")):
        notes.append("boundary/bridge/receipt-shaped module")

    if path_text.startswith(HIGH_RISK_PREFIXES) or any(
        token in path_text for token in ("DASHI/Physics/Closure/GR", "DASHI/Physics/Closure/NS", "DASHI/Physics/Closure/YM")
    ):
        risk = "avoid"
    elif adjusted >= 18 and path_text.startswith(LOW_RISK_PREFIXES) and with_count == 0:
        risk = "low"
    elif adjusted >= 10:
        risk = "medium"
    else:
        risk = "medium"

    if risk == "low":
        notes.append("likely migration-safe if public names are preserved")
    elif risk == "avoid":
        notes.append("defer broad migration; inspect only if explicitly targeted")
    else:
        notes.append("manual review needed before migration")

    return risk, adjusted, unique(notes, limit=16)


def candidate_for(path: Path) -> Candidate | None:
    text = path.read_text(encoding="utf-8")
    patterns = classify_patterns(text)
    if not patterns:
        return None

    base = raw_score(patterns)
    risk, score, notes = risk_and_notes(path, text, base)
    suggested = unique(
        core for pattern in patterns for core in pattern.suggested_cores
    )
    return Candidate(
        file=rel(path),
        risk=risk,
        score=score,
        raw_score=base,
        patterns=patterns,
        suggested_cores=suggested,
        notes=notes,
    )


def candidate_sort_key(candidate: Candidate) -> tuple[int, int, str]:
    already_adapted_rank = (
        1
        if any(note.startswith("already consumes AuthorityBoundaryCore") for note in candidate.notes)
        else 0
    )
    risk_rank = {"low": 0, "medium": 1, "avoid": 2}[candidate.risk]
    return (already_adapted_rank, risk_rank, -candidate.score, candidate.file)


def as_jsonable(candidate: Candidate) -> dict[str, object]:
    return {
        "file": candidate.file,
        "risk": candidate.risk,
        "score": candidate.score,
        "raw_score": candidate.raw_score,
        "patterns": [
            {
                "kind": pattern.kind,
                "names": pattern.names,
                "count": pattern.count,
                "suggested_cores": pattern.suggested_cores,
            }
            for pattern in candidate.patterns
        ],
        "suggested_cores": candidate.suggested_cores,
        "notes": candidate.notes,
    }


def render_markdown(candidates: list[Candidate], limit: int) -> str:
    risk_counts = {
        risk: sum(1 for candidate in candidates if candidate.risk == risk)
        for risk in ("low", "medium", "avoid")
    }
    lines = [
        "# Authority Boundary Candidate Audit",
        "",
        "Discovery-only report. Migrate by hand; do not broad-rewrite Agda proofs.",
        "",
        "## Summary",
        "",
        f"- Total candidates: {len(candidates)}",
        f"- Low risk: {risk_counts['low']}",
        f"- Medium risk: {risk_counts['medium']}",
        f"- Avoid/defer: {risk_counts['avoid']}",
        "",
        "## Top Ranked Candidates",
        "",
    ]

    for candidate in candidates[:limit]:
        pattern_labels = ", ".join(pattern.kind for pattern in candidate.patterns)
        cores = ", ".join(candidate.suggested_cores)
        notes = "; ".join(candidate.notes)
        lines.extend(
            [
                f"### {candidate.file}",
                "",
                f"- Risk: `{candidate.risk}`",
                f"- Score: `{candidate.score}` (raw `{candidate.raw_score}`)",
                f"- Suggested cores: {cores or 'none'}",
                f"- Patterns: {pattern_labels}",
                f"- Notes: {notes}",
                "",
            ]
        )
        for pattern in candidate.patterns:
            names = ", ".join(pattern.names[:10])
            suffix = "" if len(pattern.names) <= 10 else " ..."
            lines.append(
                f"  - `{pattern.kind}` ({pattern.count}): {names}{suffix}"
            )
        lines.append("")

    lines.extend(
        [
            "## Policy",
            "",
            "- Prefer low-risk receipt, bridge, promotion, biology, culture, ontology, and interop surfaces.",
            "- Preserve public receipt names, constructors, booleans, and local false projections.",
            "- Avoid GR/NS/YM analytic internals and theorem-heavy physics closures unless explicitly targeted.",
            "- Use this report to choose worker lanes; use Agda checks to validate migrations.",
            "",
        ]
    )
    return "\n".join(lines)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Rank Agda authority-boundary migration candidates."
    )
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=DEFAULT_OUTPUT_DIR,
        help="Directory for JSON/Markdown reports.",
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


def main() -> int:
    args = parse_args()
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

    print("Authority-boundary candidate audit")
    print("==================================")
    print(f"Total candidates: {len(candidates)}")
    print(f"Low risk: {risk_counts['low']}")
    print(f"Medium risk: {risk_counts['medium']}")
    print(f"Avoid/defer: {risk_counts['avoid']}")
    print()
    print("Top low-risk candidates:")
    for candidate in [c for c in candidates if c.risk == "low"][:12]:
        cores = ", ".join(candidate.suggested_cores)
        print(f"  - {candidate.file} (score {candidate.score}; {cores})")

    if not args.no_write:
        args.output_dir.mkdir(parents=True, exist_ok=True)
        json_path = args.output_dir / "authority_boundary_audit.json"
        md_path = args.output_dir / "authority_boundary_audit.md"
        payload = {
            "summary": {
                "total": len(candidates),
                "low": risk_counts["low"],
                "medium": risk_counts["medium"],
                "avoid": risk_counts["avoid"],
            },
            "candidates": [as_jsonable(candidate) for candidate in candidates],
        }
        json_path.write_text(
            json.dumps(payload, indent=2, ensure_ascii=False) + "\n",
            encoding="utf-8",
        )
        md_path.write_text(
            render_markdown(candidates, args.limit),
            encoding="utf-8",
        )
        print()
        print(f"Wrote {json_path.relative_to(ROOT)}")
        print(f"Wrote {md_path.relative_to(ROOT)}")

    print()
    print(
        "Deferred by policy: broad proof rewrites, fragile GR/NS/YM analytic "
        "internals, and theorem-heavy physics closure modules."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
