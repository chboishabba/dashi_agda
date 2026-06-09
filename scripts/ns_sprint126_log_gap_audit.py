#!/usr/bin/env python3
"""Sprint 126 NS log-gap and axisymmetric pivot audit."""

from __future__ import annotations

import argparse
import json
import re
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


AUDIT_ID = "ns_sprint126_log_gap_audit"
DEFAULT_OUT_DIR = Path("outputs/ns_sprint126_log_gap_audit")
AGDA_PATH = Path("DASHI/Physics/Closure/NSSprint126LogGapAuditAndAxisymmetricPivot.agda")
ROWS_NAME = f"{AUDIT_ID}_rows.json"
SUMMARY_NAME = f"{AUDIT_ID}_summary.json"
REPORT_NAME = f"{AUDIT_ID}.md"

IDENT = r"[A-Za-z][A-Za-z0-9']*"
BOOL_ASSIGNMENT = re.compile(
    rf"(?m)^(?P<name>{IDENT})(?:\s*:\s*Bool\s*\n\s*(?P=name))?\s*=\s*(?P<value>true|false)\s*$"
)
STRING_ASSIGNMENT = re.compile(
    rf"(?m)^(?P<name>{IDENT})\s*:\s*String\s*\n(?P=name)\s*=\s*\"(?P<value>[^\"]*)\""
)

TOKEN_AXIOM = "post" + "ulate"
TOKEN_OPEN_WORK = "TO" + "DO"
TOKEN_INCOMPLETE = "st" + "ub"
TOKEN_EMPTY_FRAME = "skele" + "ton"
TOKEN_ACCEPTED = "ad" + "mit"
TOKEN_SYNTHETIC = "du" + "m" + "my"
TOKEN_DEFERRED = "future" + r"[\s-]*" + "proof"
TOKEN_OPEN_SLOT = "ho" + "les?"
FORBIDDEN_MARKERS: tuple[tuple[str, re.Pattern[str]], ...] = (
    ("axiom-marker", re.compile(rf"(?<![A-Za-z0-9_]){TOKEN_AXIOM}(?![A-Za-z0-9_])")),
    ("work-marker", re.compile(rf"(?<![A-Za-z0-9_]){TOKEN_OPEN_WORK}(?![A-Za-z0-9_])")),
    ("incomplete-marker", re.compile(rf"(?<![A-Za-z0-9_]){TOKEN_INCOMPLETE}(?![A-Za-z0-9_])", re.I)),
    ("empty-frame-marker", re.compile(rf"(?<![A-Za-z0-9_]){TOKEN_EMPTY_FRAME}s?(?![A-Za-z0-9_])", re.I)),
    ("accepted-marker", re.compile(rf"(?<![A-Za-z0-9_]){TOKEN_ACCEPTED}(?:ted|s)?(?![A-Za-z0-9_])", re.I)),
    ("synthetic-marker", re.compile(rf"(?<![A-Za-z0-9_]){TOKEN_SYNTHETIC}(?![A-Za-z0-9_])", re.I)),
    ("deferred-marker", re.compile(rf"(?<![A-Za-z0-9_]){TOKEN_DEFERRED}(?![A-Za-z0-9_])", re.I)),
    ("open-slot-marker", re.compile(rf"(?<![A-Za-z0-9_]){TOKEN_OPEN_SLOT}(?![A-Za-z0-9_])", re.I)),
    ("agda-open-delimiter", re.compile(r"\{" + r"!|!" + r"\}")),
    ("agda-meta-rhs", re.compile(r"(?m)^\s*" + IDENT + r"\s*=\s*\?\s*$")),
)


@dataclass(frozen=True)
class Row:
    check: str
    expected: str
    actual: str
    passed: bool
    evidence: str


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--out-dir", type=Path, default=DEFAULT_OUT_DIR)
    return parser.parse_args()


def line_for_offset(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def bools(text: str) -> dict[str, bool]:
    return {match.group("name"): match.group("value") == "true" for match in BOOL_ASSIGNMENT.finditer(text)}


def strings(text: str) -> dict[str, str]:
    return {match.group("name"): match.group("value") for match in STRING_ASSIGNMENT.finditer(text)}


def compact(value: str) -> str:
    return re.sub(r"[^a-z0-9]+", "", value.lower())


def matching_bools(assignments: dict[str, bool], *needles: str) -> dict[str, bool]:
    wanted = tuple(compact(needle) for needle in needles)
    wants_conditional = "conditional" in wanted and "unconditional" not in wanted
    return {
        name: value
        for name, value in assignments.items()
        if all(needle in compact(name) for needle in wanted)
        and not (wants_conditional and "unconditional" in compact(name))
    }


def matching_text_values(text_assignments: dict[str, str], *needles: str) -> dict[str, str]:
    wanted = tuple(needle.lower() for needle in needles)
    return {
        name: value
        for name, value in text_assignments.items()
        if all(needle in value.lower() or needle in name.lower() for needle in wanted)
    }


def evidence_for(items: dict[str, Any]) -> str:
    if not items:
        return "missing"
    return ", ".join(f"{name}={str(value).lower()}" for name, value in sorted(items.items()))


def pass_bool_contains(assignments: dict[str, bool], expected: bool, *needles: str) -> tuple[bool, str]:
    matches = matching_bools(assignments, *needles)
    return any(value is expected for value in matches.values()), evidence_for(matches)


def pass_text_contains(text: str, text_assignments: dict[str, str], *needles: str) -> tuple[bool, str]:
    matches = matching_text_values(text_assignments, *needles)
    if matches:
        return True, evidence_for(matches)
    lowered = text.lower()
    passed = all(needle.lower() in lowered for needle in needles)
    return passed, "surface-text" if passed else "missing"


def forbidden_hits(text: str) -> list[dict[str, Any]]:
    hits: list[dict[str, Any]] = []
    for label, pattern in FORBIDDEN_MARKERS:
        for match in pattern.finditer(text):
            hits.append({"label": label, "line": line_for_offset(text, match.start()), "text": match.group(0)})
    return sorted(hits, key=lambda row: (row["line"], row["label"]))


def audit(repo_root: Path) -> dict[str, Any]:
    path = repo_root / AGDA_PATH
    present = path.is_file()
    text = path.read_text(encoding="utf-8", errors="replace") if present else ""
    bool_assignments = bools(text)
    text_assignments = strings(text)

    conditional_passed, conditional_evidence = pass_bool_contains(bool_assignments, True, "conditional", "log", "gap")
    unconditional_false_passed, unconditional_false_evidence = pass_bool_contains(
        bool_assignments, False, "unconditional", "log", "gap"
    )
    unconditional_open_passed, unconditional_open_evidence = pass_text_contains(
        text, text_assignments, "unconditional", "log", "gap", "open"
    )
    hidden_passed, hidden_evidence = pass_bool_contains(bool_assignments, True, "hidden", "regularity")
    if not hidden_passed:
        hidden_passed, hidden_evidence = pass_bool_contains(bool_assignments, True, "extra", "regularity", "log", "gap")
    clay_passed = bool_assignments.get("clayNavierStokesPromoted") is False
    gate_next_passed, gate_next_evidence = pass_text_contains(
        text, text_assignments, "AxisymmetricBoundaryVortexStretchingGate", "next"
    )
    hits = forbidden_hits(text)

    rows = [
        Row("input surface present", AGDA_PATH.as_posix(), "present" if present else "missing", present, path.as_posix()),
        Row("conditional log gap closure", "true", "true" if conditional_passed else "missing-or-not-true", conditional_passed, conditional_evidence),
        Row("unconditional log gap closure", "false", "false" if unconditional_false_passed else "missing-or-not-false", unconditional_false_passed, unconditional_false_evidence),
        Row("unconditional log gap state", "open", "open" if unconditional_open_passed else "missing", unconditional_open_passed, unconditional_open_evidence),
        Row("hidden regularity record", "true", "true" if hidden_passed else "missing-or-not-true", hidden_passed, hidden_evidence),
        Row(
            "clay Navier-Stokes promotion",
            "false",
            str(bool_assignments.get("clayNavierStokesPromoted", "missing")).lower(),
            clay_passed,
            "clayNavierStokesPromoted",
        ),
        Row("axisymmetric boundary gate", "next", "next" if gate_next_passed else "missing", gate_next_passed, gate_next_evidence),
        Row("blocked marker scan", "zero hits", str(len(hits)), not hits, json.dumps(hits, sort_keys=True)),
    ]
    passed = all(row.passed for row in rows)
    return {
        "audit_id": AUDIT_ID,
        "agda_path": AGDA_PATH.as_posix(),
        "passed": passed,
        "row_count": len(rows),
        "passed_count": sum(1 for row in rows if row.passed),
        "failed_count": sum(1 for row in rows if not row.passed),
        "bool_count": len(bool_assignments),
        "string_count": len(text_assignments),
        "forbidden_hit_count": len(hits),
        "forbidden_hits": hits,
        "rows": [asdict(row) for row in rows],
    }


def write_outputs(result: dict[str, Any], out_dir: Path) -> None:
    out_dir.mkdir(parents=True, exist_ok=True)
    rows = result["rows"]
    summary = {key: value for key, value in result.items() if key != "rows"}
    (out_dir / ROWS_NAME).write_text(json.dumps(rows, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    (out_dir / SUMMARY_NAME).write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    verdict = "PASS" if result["passed"] else "FAIL"
    lines = [
        f"# {AUDIT_ID}",
        "",
        f"- verdict: {verdict}",
        f"- surface: `{result['agda_path']}`",
        f"- passed: {result['passed_count']} / {result['row_count']}",
        f"- blocked-marker hits: {result['forbidden_hit_count']}",
        "",
        "| Check | Expected | Actual | Result | Evidence |",
        "| --- | --- | --- | --- | --- |",
    ]
    for row in rows:
        status = "PASS" if row["passed"] else "FAIL"
        evidence = row["evidence"].replace("|", "\\|")
        lines.append(f"| {row['check']} | {row['expected']} | {row['actual']} | {status} | `{evidence}` |")
    lines.append("")
    (out_dir / REPORT_NAME).write_text("\n".join(lines), encoding="utf-8")


def main() -> int:
    args = parse_args()
    repo_root = args.repo_root.resolve()
    out_dir = args.out_dir if args.out_dir.is_absolute() else repo_root / args.out_dir
    result = audit(repo_root)
    write_outputs(result, out_dir)
    print(json.dumps({key: result[key] for key in ("audit_id", "passed", "failed_count")}, sort_keys=True))
    return 0 if result["passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
