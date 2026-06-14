#!/usr/bin/env python3
"""Diagnostic audit of the internal Balaban Option-B gap from repo-local facts.

The audit is intentionally fail-closed: B1-B5 may be present as boundary
surfaces, but no row is allowed to promote Clay/YM closure from those surfaces.
It is a diagnostic/no-promotion script, not a theorem proof.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Iterable


AUDIT_ID = "ym_option_b_gap_audit"
OPTION_B_AGDA = Path("DASHI/Physics/Closure/OptionBNativePolymerFiveLemmaBoundaryReceipt.agda")
OPTION_A_AGDA = Path("DASHI/Physics/Closure/YMBalabanOptionATheoremIntakeReceipt.agda")
PAPER3 = Path("Docs/papers/live/Paper3YangMillsClayDraft.md")
MANIFEST = Path("Docs/papers/generated/core_papers_theorem_var_manifest.json")

REQUIRED_SOURCE_FILES = (OPTION_B_AGDA, OPTION_A_AGDA, PAPER3)
OPTIONAL_SOURCE_FILES = (MANIFEST,)

INCOMPLETE_PATTERNS: tuple[tuple[str, re.Pattern[str]], ...] = (
    ("postulate", re.compile(r"(?<![A-Za-z0-9_])post" + r"ulate(?![A-Za-z0-9_])")),
    ("todo", re.compile(r"(?<![A-Za-z0-9_])TO" + r"DO(?![A-Za-z0-9_])")),
    ("stub", re.compile(r"(?<![A-Za-z0-9_])st" + r"ub(?![A-Za-z0-9_])", re.IGNORECASE)),
    ("agda-hole", re.compile(re.escape("{" + "!") + r"|" + re.escape("!" + "}"))),
    ("rhs-meta", re.compile(r"(?m)^\s*[A-Za-z][A-Za-z0-9']*\s*=\s*\?\s*$")),
)

PROMOTION_TRUE_PATTERNS: tuple[re.Pattern[str], ...] = (
    re.compile(r"(?m)^\s*clayYangMillsPromoted\s*=\s*true\s*$"),
    re.compile(r"(?m)^\s*continuumYangMillsConstructed\s*=\s*true\s*$"),
    re.compile(r"(?m)^\s*massGapPromoted\s*=\s*true\s*$"),
    re.compile(r'"clayYangMillsPromoted"\s*:\s*true'),
    re.compile(r'"continuumYangMillsConstructed"\s*:\s*true'),
    re.compile(r'"massGapPromoted"\s*:\s*true'),
)


@dataclass(frozen=True)
class GateSpec:
    gate_id: str
    constructor: str
    title: str
    difficulty: str
    support_terms: tuple[str, ...]
    closure_blockers: tuple[str, ...]
    missing_content: tuple[str, ...]
    next_artifact: str


GATES: tuple[GateSpec, ...] = (
    GateSpec(
        gate_id="B1",
        constructor="B1CasimirSuppressionSU2SU3Constants",
        title="Uniform-in-N Casimir/walk-bound constants",
        difficulty="high",
        support_terms=(
            "CasimirSuppressionConstant",
            "su2FundamentalCasimir",
            "su3FundamentalCasimir",
            "su2SuppressionBelowSU3",
            "Casimir suppression",
            "walk-bound",
        ),
        closure_blockers=(
            "noContinuumYangMillsConstruction",
            "noMassGapPromotion",
            "noClayYangMillsPromotion",
        ),
        missing_content=(
            "uniform-in-N walk-count constant ledger tied to the Casimir floor",
            "proof that the recorded SU2/SU3 finite constants control every polymer scale",
            "Agda theorem closing the bound without relying on Balaban authority intake",
        ),
        next_artifact="B1 uniform Casimir/walk-bound theorem module with explicit N-independent constants",
    ),
    GateSpec(
        gate_id="B2",
        constructor="B2PolymerLocalization",
        title="Polymer localization/walk expansion",
        difficulty="high",
        support_terms=(
            "PolymerLocalizationSurface",
            "canonicalPolymerLocalizationSurface",
            "finiteCarrierSupport",
            "localBoundaryDiameter",
            "polymer expansion",
            "polymer localization",
        ),
        closure_blockers=(
            "continuumLocalizationClaimedIsFalse",
            "noContinuumSupportClaim",
        ),
        missing_content=(
            "infinite-volume polymer localization theorem",
            "walk expansion with compatible-collection counting beyond finite carrier support",
            "boundary/large-diameter tail estimate that survives the continuum limit",
        ),
        next_artifact="B2 native polymer localization and walk-expansion proof surface",
    ),
    GateSpec(
        gate_id="B3",
        constructor="B3DASHIBalabanActivityBoundAndKPCondition",
        title="KP/activity/base-case constants",
        difficulty="very_high",
        support_terms=(
            "DASHIBalabanActivityKPSurface",
            "canonicalDASHIBalabanActivityKPSurface",
            "activityBelowOne",
            "weightedKPBoundBelowOne",
            "kpConditionClosed",
            "Kotecky",
            "KP",
            "activity",
        ),
        closure_blockers=(
            "weightedKPBoundBelowOneIsFalse",
            "weightedKPFailsAtRecordedBeta",
            "kpConditionClosedIsFalse",
            "noKPClosureAtRecordedIntermediateBeta",
        ),
        missing_content=(
            "closed Kotecky-Preiss weighted-neighborhood inequality at the recorded scale",
            "base-case constants that beat branching and activity losses",
            "machine-checkable bridge from activity arithmetic to Balaban-compatible polymer summability",
        ),
        next_artifact="B3 KP/activity constant ledger with a closed weighted KP inequality",
    ),
    GateSpec(
        gate_id="B4",
        constructor="B4TraceNormConvergenceFromSummability",
        title="Trace-norm norm bridge",
        difficulty="very_high",
        support_terms=(
            "TraceNormFromSummabilitySurface",
            "canonicalTraceNormFromSummabilitySurface",
            "traceNormCauchyCriterionRecorded",
            "traceNormLimitConstructed",
            "trace-norm",
            "norm-resolvent",
        ),
        closure_blockers=(
            "traceNormLimitConstructedIsFalse",
            "noOperatorLimitPromotion",
        ),
        missing_content=(
            "operator-level trace-norm limit construction from the summability ledger",
            "norm bridge from polymer sums to the vacuum-orthogonal transfer sector",
            "compatibility proof with Mosco/norm-resolvent transfer claims consumed by H3a",
        ),
        next_artifact="B4 trace-norm transfer bridge proving the operator limit, not only Cauchy bookkeeping",
    ),
    GateSpec(
        gate_id="B5",
        constructor="B5IntermediateBetaRGInductionWarning",
        title="Intermediate-beta RG induction",
        difficulty="very_high",
        support_terms=(
            "IntermediateBetaRGInductionWarningSurface",
            "canonicalIntermediateBetaRGInductionWarningSurface",
            "rgInductionAllowed",
            "warningActive",
            "intermediate-beta",
            "Balaban induction",
            "RG induction",
        ),
        closure_blockers=(
            "rgInductionAllowedIsFalse",
            "warningActiveIsTrue",
            "noBalabanRGTheorem",
            "noBalabanInductionPromotion",
        ),
        missing_content=(
            "RG induction base and step below the recorded beta threshold",
            "large-field/small-field decomposition that closes the Balaban multiscale recurrence",
            "proof replacing the Option-A external theorem intake with repo-native induction",
        ),
        next_artifact="B5 intermediate-beta Balaban RG induction module with closed recurrence and promotion guard",
    ),
)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument(
        "--format",
        choices=("json", "md"),
        default="json",
        help="Output format. Defaults to JSON.",
    )
    parser.add_argument("--pretty", action="store_true", help="Pretty-print JSON output.")
    return parser.parse_args()


def rel(repo_root: Path, path: Path) -> str:
    try:
        return path.resolve().relative_to(repo_root.resolve()).as_posix()
    except ValueError:
        return path.as_posix()


def read_sources(repo_root: Path) -> tuple[dict[str, str], list[dict[str, str]]]:
    sources: dict[str, str] = {}
    errors: list[dict[str, str]] = []
    for source in REQUIRED_SOURCE_FILES + OPTIONAL_SOURCE_FILES:
        path = repo_root / source
        key = source.as_posix()
        if not path.exists():
            if source in REQUIRED_SOURCE_FILES:
                errors.append({"path": key, "reason": "missing required source file"})
            continue
        try:
            sources[key] = path.read_text(encoding="utf-8", errors="replace")
        except OSError as exc:
            errors.append({"path": key, "reason": f"unreadable source file: {exc}"})
    return sources, errors


def line_number(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def compact_line(line: str, limit: int = 180) -> str:
    value = " ".join(line.strip().split())
    if len(value) <= limit:
        return value
    return value[: limit - 3] + "..."


def line_hits(path: str, text: str, pattern: re.Pattern[str], limit: int = 8) -> list[dict[str, Any]]:
    hits: list[dict[str, Any]] = []
    lines = text.splitlines()
    offsets: list[int] = []
    cursor = 0
    for line in lines:
        offsets.append(cursor)
        cursor += len(line) + 1
    for index, line in enumerate(lines):
        if pattern.search(line):
            hits.append({"path": path, "line": index + 1, "text": compact_line(line)})
            if len(hits) >= limit:
                break
    if not hits:
        for match in pattern.finditer(text):
            hits.append(
                {
                    "path": path,
                    "line": line_number(text, match.start()),
                    "text": compact_line(lines[line_number(text, match.start()) - 1]),
                }
            )
            if len(hits) >= limit:
                break
    return hits


def source_contains_gate_id(source_texts: Iterable[str], gate_id: str) -> bool:
    pattern = re.compile(rf"(?<![A-Za-z0-9_]){re.escape(gate_id)}(?![A-Za-z0-9_])")
    return any(pattern.search(text) for text in source_texts)


def support_for_gate(sources: dict[str, str], spec: GateSpec) -> list[dict[str, Any]]:
    terms = (spec.constructor,) + spec.support_terms + spec.closure_blockers
    pattern = re.compile("|".join(re.escape(term) for term in terms), re.IGNORECASE)
    support: list[dict[str, Any]] = []
    for path, text in sources.items():
        hits = line_hits(path, text, pattern)
        if hits:
            support.append({"path": path, "evidence": hits})
    return support


def status_for_gate(
    spec: GateSpec,
    support: list[dict[str, Any]],
    sources: dict[str, str],
    missing_gate_ids: set[str],
) -> str:
    if spec.gate_id in missing_gate_ids:
        return "missing_gate_id_fail_closed"
    source_blob = "\n".join(sources.values()).lower()
    blocker_present = any(blocker.lower() in source_blob for blocker in spec.closure_blockers)
    if blocker_present:
        return "recorded_boundary_blocked"
    if support:
        return "support_recorded_no_promotion"
    return "unsupported_fail_closed"


def scan_incomplete_markers(sources: dict[str, str]) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for path, text in sources.items():
        for marker, pattern in INCOMPLETE_PATTERNS:
            for hit in line_hits(path, text, pattern, limit=3):
                rows.append({"marker": marker, **hit})
    return rows


def scan_promotion_true(sources: dict[str, str]) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for path, text in sources.items():
        for pattern in PROMOTION_TRUE_PATTERNS:
            for hit in line_hits(path, text, pattern, limit=4):
                rows.append(hit)
    return rows


def manifest_rows(sources: dict[str, str]) -> list[dict[str, Any]]:
    text = sources.get(MANIFEST.as_posix())
    if text is None:
        return []
    try:
        payload = json.loads(text)
    except json.JSONDecodeError as exc:
        return [{"path": MANIFEST.as_posix(), "manifest_error": f"invalid JSON: {exc}"}]
    rows: list[dict[str, Any]] = []

    def walk(value: Any) -> Iterable[Any]:
        yield value
        if isinstance(value, dict):
            for child in value.values():
                yield from walk(child)
        elif isinstance(value, list):
            for child in value:
                yield from walk(child)

    for item in walk(payload):
        if not isinstance(item, dict):
            continue
        blob = json.dumps(item, sort_keys=True)
        if "Option B" in blob or "Option-B" in blob or "Balaban" in blob or "polymer" in blob:
            row = {
                "lemma": item.get("lemma"),
                "exact_var": item.get("exact_var"),
                "authority": item.get("authority"),
                "governance_note": item.get("governance_note"),
            }
            if any(value is not None for value in row.values()):
                rows.append(row)
    return rows[:12]


def build_audit(repo_root: Path) -> dict[str, Any]:
    repo_root = repo_root.resolve()
    sources, source_errors = read_sources(repo_root)
    known_source_texts = list(sources.values())
    missing_gate_ids = {
        spec.gate_id for spec in GATES if not source_contains_gate_id(known_source_texts, spec.gate_id)
    }

    promotion_true_hits = scan_promotion_true(sources)
    incomplete_marker_hits = scan_incomplete_markers(sources)

    gates: list[dict[str, Any]] = []
    for spec in GATES:
        support = support_for_gate(sources, spec)
        gates.append(
            {
                "gate_id": spec.gate_id,
                "title": spec.title,
                "status": status_for_gate(spec, support, sources, missing_gate_ids),
                "difficulty": spec.difficulty,
                "current_support_files": support,
                "missing_content": list(spec.missing_content),
                "promotion_allowed": False,
                "clay_promotion": False,
                "next_artifact": spec.next_artifact,
            }
        )

    fail_closed_reasons: list[str] = []
    fail_closed_reasons.extend(f"{row['path']}: {row['reason']}" for row in source_errors)
    fail_closed_reasons.extend(f"missing required gate id {gate_id}" for gate_id in sorted(missing_gate_ids))
    if promotion_true_hits:
        fail_closed_reasons.append("promotion true marker detected in inspected sources")

    all_supported = all(gate["current_support_files"] for gate in gates)
    all_blocked = all(not gate["promotion_allowed"] and not gate["clay_promotion"] for gate in gates)
    audit_status = "fail_closed" if fail_closed_reasons else "blocked_no_promotion"

    return {
        "audit_id": AUDIT_ID,
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "repo_root": rel(repo_root, repo_root),
        "format_version": 1,
        "source_files": [
            {
                "path": path,
                "required": Path(path) in REQUIRED_SOURCE_FILES,
                "present": path in sources,
                "bytes": len(sources[path].encode("utf-8")) if path in sources else 0,
            }
            for path in [source.as_posix() for source in REQUIRED_SOURCE_FILES + OPTIONAL_SOURCE_FILES]
        ],
        "audit_status": audit_status,
        "promotion_allowed": False,
        "clay_promotion": False,
        "fail_closed": True,
        "fail_closed_reasons": fail_closed_reasons,
        "required_gate_ids": [spec.gate_id for spec in GATES],
        "missing_required_gate_ids": sorted(missing_gate_ids),
        "gate_count": len(gates),
        "all_gate_support_recorded": all_supported,
        "all_gates_block_promotion": all_blocked,
        "gates": gates,
        "manifest_balaban_option_rows": manifest_rows(sources),
        "promotion_true_hits": promotion_true_hits,
        "incomplete_marker_hits": incomplete_marker_hits,
        "summary": {
            "O": "Audit the repo-local internal Balaban Option-B gap across the Option-B receipt, Option-A intake receipt, Paper 3 draft, and generated theorem manifest if present.",
            "R": "B1-B5 gate IDs must be present in inspected sources; JSON is default; Markdown is available; promotion fields remain false.",
            "C": "The CLI is self-contained in scripts/ym_option_b_gap_audit.py and uses only Python stdlib readers/parsers.",
            "S": f"{len(gates)} gates scanned; audit_status={audit_status}; missing_gate_ids={sorted(missing_gate_ids)}.",
            "L": "Evidence is textual and repo-local; it records support surfaces and blockers as diagnostic evidence, not external theorem validity.",
            "P": "Promotion is disallowed until every missing_content item is replaced by proof-bearing Agda/paper artifacts.",
            "G": "Fail-closed governance: any missing source/gate ID or true promotion marker keeps Clay promotion false; no promotion follows from this diagnostic audit.",
            "F": "Next artifact lane is per gate, with B3/B5 carrying the main Balaban/KP/RG closure burden.",
        },
    }


def render_md(audit: dict[str, Any]) -> str:
    lines = [
        f"# {audit['audit_id']}",
        "",
        f"- status: `{audit['audit_status']}`",
        f"- promotion_allowed: `{str(audit['promotion_allowed']).lower()}`",
        f"- clay_promotion: `{str(audit['clay_promotion']).lower()}`",
        f"- missing_required_gate_ids: `{', '.join(audit['missing_required_gate_ids']) or 'none'}`",
        "",
        "## Gates",
        "",
        "| gate_id | title | status | difficulty | next_artifact |",
        "| --- | --- | --- | --- | --- |",
    ]
    for gate in audit["gates"]:
        lines.append(
            "| {gate_id} | {title} | `{status}` | {difficulty} | {next_artifact} |".format(**gate)
        )
    lines.extend(["", "## Missing Content", ""])
    for gate in audit["gates"]:
        lines.append(f"### {gate['gate_id']} {gate['title']}")
        for item in gate["missing_content"]:
            lines.append(f"- {item}")
        lines.append("")
    lines.extend(["## Support Files", ""])
    for gate in audit["gates"]:
        paths = [row["path"] for row in gate["current_support_files"]]
        lines.append(f"- `{gate['gate_id']}`: {', '.join(f'`{path}`' for path in paths) or '`none`'}")
    if audit["fail_closed_reasons"]:
        lines.extend(["", "## Fail-Closed Reasons", ""])
        for reason in audit["fail_closed_reasons"]:
            lines.append(f"- {reason}")
    lines.extend(["", "## O/R/C/S/L/P/G/F", ""])
    for key, value in audit["summary"].items():
        lines.append(f"- {key}: {value}")
    return "\n".join(lines) + "\n"


def main() -> int:
    args = parse_args()
    audit = build_audit(args.repo_root)
    if args.format == "md":
        sys.stdout.write(render_md(audit))
    else:
        indent = 2 if args.pretty else None
        sys.stdout.write(json.dumps(audit, indent=indent, sort_keys=True))
        sys.stdout.write("\n")
    return 2 if audit["missing_required_gate_ids"] or any("missing required source" in reason for reason in audit["fail_closed_reasons"]) else 0


if __name__ == "__main__":
    raise SystemExit(main())
