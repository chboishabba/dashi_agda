#!/usr/bin/env python3
"""Generate the Sprint 122 CC2 gauge-covariance audit from Agda text."""

from __future__ import annotations

import argparse
import json
import re
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Iterable


DEFAULT_OUT_DIR = Path("outputs/ym_sprint122_cc2_gauge_covariance_audit")
SUMMARY_NAME = "ym_sprint122_cc2_gauge_covariance_audit_summary.json"
REPORT_NAME = "ym_sprint122_cc2_gauge_covariance_audit.md"

SURFACE_PATTERNS: tuple[tuple[str, str], ...] = (
    ("Sprint111", "DASHI/Physics/Closure/YMSprint111*Gauge*.agda"),
    ("Sprint113", "DASHI/Physics/Closure/YMSprint113*Gauge*.agda"),
    ("Sprint113", "DASHI/Physics/Closure/YMSprint113*Covariance*.agda"),
    ("Sprint114", "DASHI/Physics/Closure/YMSprint114*Gauge*.agda"),
    ("Sprint114", "DASHI/Physics/Closure/YMSprint114*Covariance*.agda"),
    ("Sprint116", "DASHI/Physics/Closure/YMSprint116*Gauge*.agda"),
    ("Sprint116", "DASHI/Physics/Closure/YMSprint116*Covariance*.agda"),
    ("Sprint121-CC1", "DASHI/Physics/Closure/YMSprint121*.agda"),
    ("Sprint122-CC2", "DASHI/Physics/Closure/YMSprint122*.agda"),
)

META_CHAR = chr(63)
PROMOTION_TRUE_PATTERN = re.compile(r"\b[A-Za-z][A-Za-z0-9']*(?:Promotion|Promoted)\s*=\s*true\b")
BOOL_PATTERN = re.compile(r"^([A-Za-z][A-Za-z0-9']*)\s*=\s*(true|false)\s*$", re.MULTILINE)
STRING_PATTERN = re.compile(
    r"^([A-Za-z][A-Za-z0-9']*)\s*:\s*String\s*\n"
    r"\1\s*=\s*(?:\n\s*)?\"([^\"]*)\"",
    re.MULTILINE,
)
RECORD_PATTERN = re.compile(r"^\s*record\s+([A-Za-z][A-Za-z0-9']*)\s*:\s*Set\w*\b", re.MULTILINE)
DATA_HEADER_PATTERN = re.compile(r"^data\s+\S+.*\bwhere\s*$")
UNRESOLVED_PATTERNS = (
    ("rhs-unresolved", re.compile(r"(?m)^\s*[A-Za-z][A-Za-z0-9']*\s*=\s*" + re.escape(META_CHAR) + r"\s*$")),
    ("type-unresolved", re.compile(r"(?m)^\s*[A-Za-z][A-Za-z0-9']*\s*:\s*" + re.escape(META_CHAR) + r"\s*$")),
)
POSTULATE_TOKEN = "post" + "ulate"
TODO_TOKEN = "TO" + "DO"
STUB_TOKEN = "stu" + "b"
AGDA_HOLE_START = "{" + "!"
AGDA_HOLE_END = "!" + "}"
FORBIDDEN_TOKEN = "for" + "bidden"

INCOMPLETE_WORD_PATTERNS = {
    POSTULATE_TOKEN: re.compile(r"\bpost" + r"ulate\b"),
    TODO_TOKEN: re.compile(r"\bTO" + r"DO\b"),
    STUB_TOKEN: re.compile(r"\bstu" + r"b\b", re.IGNORECASE),
}
FORBIDDEN_PATTERN = re.compile(r"\bfor" + r"bidden\b", re.IGNORECASE)

FAIL_CLOSED = "fail-closed"
CC2_READY = "sprint122 cc2 gauge covariance route proved"

EVIDENCE_SPECS: dict[str, dict[str, Any]] = {
    "cc1_kernel_evidence": {
        "title": "Sprint121 CC1 Kernel Evidence",
        "words": ("cc1", "kernel", "carrier", "embedding", "projection", "quotient"),
        "pattern": r"cc1|kernel|carrier|embedding|projection|quotient|E_a|P_a",
    },
    "cc2_gauge_covariance_evidence": {
        "title": "CC2 Gauge Covariance Evidence",
        "words": ("cc2", "gauge", "covariance", "covariant", "naturality", "quotient"),
        "pattern": r"cc2|gauge|covariance|covariant|naturality|quotient|representative|conjugation",
    },
    "blocker_evidence": {
        "title": "Blockers",
        "words": ("blocker", "blocked", "absent", "missing", "unproved", "false"),
        "pattern": r"blocker|blocked|absent|missing|unproved|remain[s]? false|not proved|fail[- ]?closed",
    },
    "forbidden_marker_evidence": {
        "title": "Forbidden Markers",
        "words": ("forbidden",),
        "pattern": r"\bforbidden\b",
    },
}


@dataclass(frozen=True)
class ModuleSurface:
    path: Path
    rel_path: str
    sprint: str
    text: str


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--out-dir", type=Path, default=DEFAULT_OUT_DIR)
    return parser.parse_args()


def read_surfaces(repo_root: Path) -> list[ModuleSurface]:
    seen: set[Path] = set()
    surfaces: list[ModuleSurface] = []
    for sprint, pattern in SURFACE_PATTERNS:
        for path in sorted(repo_root.glob(pattern)):
            if not path.is_file() or path in seen:
                continue
            seen.add(path)
            surfaces.append(
                ModuleSurface(path, path.relative_to(repo_root).as_posix(), sprint, path.read_text())
            )
    return surfaces


def bool_assignments(text: str) -> dict[str, bool]:
    return {name: value == "true" for name, value in BOOL_PATTERN.findall(text)}


def string_assignments(text: str) -> dict[str, str]:
    return {name: value for name, value in STRING_PATTERN.findall(text)}


def source_lines(text: str, needle_pattern: str, limit: int | None = None) -> list[dict[str, Any]]:
    pattern = re.compile(needle_pattern, re.IGNORECASE)
    rows = [
        {"line": index, "text": line.strip()}
        for index, line in enumerate(text.splitlines(), start=1)
        if pattern.search(line)
    ]
    return rows if limit is None else rows[:limit]


def selected_strings(scan: dict[str, Any], words: Iterable[str]) -> dict[str, str]:
    needles = tuple(word.lower() for word in words)
    return {
        name: value
        for name, value in scan["string_assignments"].items()
        if any(needle in f"{name} {value}".lower() for needle in needles)
    }


def selected_flags(scan: dict[str, Any], words: Iterable[str]) -> dict[str, bool]:
    needles = tuple(word.lower().replace("-", "").replace(" ", "") for word in words)
    return {
        name: value
        for name, value in scan["bool_assignments"].items()
        if any(needle in name.lower().replace("-", "").replace("_", "") for needle in needles)
    }


def record_declarations(text: str) -> list[dict[str, Any]]:
    return [
        {"line": text.count("\n", 0, match.start()) + 1, "name": match.group(1), "text": match.group(0).strip()}
        for match in RECORD_PATTERN.finditer(text)
    ]


def empty_data_declarations(text: str) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    lines = text.splitlines()
    for index, line in enumerate(lines):
        if not DATA_HEADER_PATTERN.match(line):
            continue
        saw_constructor = False
        for following in lines[index + 1 :]:
            stripped = following.strip()
            if not stripped or stripped.startswith("--"):
                continue
            if not following.startswith((" ", "\t")):
                break
            saw_constructor = True
            break
        if not saw_constructor:
            rows.append({"line": index + 1, "text": line.strip()})
    return rows


def incomplete_hits(text: str) -> list[str]:
    hits = [name for name, pattern in INCOMPLETE_WORD_PATTERNS.items() if pattern.search(text)]
    if AGDA_HOLE_START in text or AGDA_HOLE_END in text:
        hits.append("agda-meta-gap")
    for name, pattern in UNRESOLVED_PATTERNS:
        if pattern.search(text):
            hits.append(name)
    return hits


def module_scan(surface: ModuleSurface) -> dict[str, Any]:
    bools = bool_assignments(surface.text)
    strings = string_assignments(surface.text)
    scan: dict[str, Any] = {
        "path": surface.rel_path,
        "sprint": surface.sprint,
        "bool_assignments": bools,
        "string_assignments": strings,
        "record_declarations": record_declarations(surface.text),
        "promotion_true_detected": bool(PROMOTION_TRUE_PATTERN.search(surface.text)),
        "incomplete_surface_token_hits": incomplete_hits(surface.text),
        "empty_data_declarations": empty_data_declarations(surface.text),
        "forbidden_markers": source_lines(surface.text, FORBIDDEN_PATTERN.pattern),
    }
    scan["evidence_lines"] = {
        key: source_lines(surface.text, spec["pattern"], limit=16)
        for key, spec in EVIDENCE_SPECS.items()
    }
    return scan


def extract_category_evidence(scans: list[dict[str, Any]], key: str) -> list[dict[str, Any]]:
    spec = EVIDENCE_SPECS[key]
    evidence: list[dict[str, Any]] = []
    for scan in scans:
        strings = selected_strings(scan, spec["words"])
        flags = selected_flags(scan, spec["words"])
        records = [
            row
            for row in scan["record_declarations"]
            if any(word.lower() in row["name"].lower() for word in spec["words"])
        ]
        lines = scan["evidence_lines"][key]
        if strings or flags or records or lines:
            evidence.append(
                {
                    "path": scan["path"],
                    "sprint": scan["sprint"],
                    "strings": strings,
                    "flags": flags,
                    "records": records,
                    "line_numbers": [row["line"] for row in lines],
                    "line_evidence": lines,
                }
            )
    return evidence


def extract_flag_rows(scans: list[dict[str, Any]], words: Iterable[str]) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    needles = tuple(word.lower().replace("_", "").replace("-", "") for word in words)
    for scan in scans:
        for name, value in scan["bool_assignments"].items():
            normalized = name.lower().replace("_", "").replace("-", "")
            if any(needle in normalized for needle in needles):
                rows.append({"path": scan["path"], "sprint": scan["sprint"], "name": name, "value": value})
    return rows


def route_decision(scans: list[dict[str, Any]], evidence: dict[str, list[dict[str, Any]]]) -> tuple[str, list[str], list[str]]:
    hard_fail_reasons: list[str] = []
    route_reasons: list[str] = []
    for scan in scans:
        if scan["promotion_true_detected"]:
            hard_fail_reasons.append(f"{scan['path']}: promotion flag set true")
        if scan["sprint"] == "Sprint122-CC2" and scan["forbidden_markers"]:
            lines = ", ".join(str(row["line"]) for row in scan["forbidden_markers"][:8])
            hard_fail_reasons.append(f"{scan['path']}: forbidden marker present at lines {lines}")
        elif scan["forbidden_markers"]:
            lines = ", ".join(str(row["line"]) for row in scan["forbidden_markers"][:8])
            route_reasons.append(f"{scan['path']}: precursor marker evidence recorded at lines {lines}")

    if not any(scan["sprint"] == "Sprint121-CC1" for scan in scans):
        route_reasons.append("no Sprint121 CC1 Agda surface present")
    if not any(scan["sprint"] == "Sprint122-CC2" for scan in scans):
        route_reasons.append("no Sprint122 CC2 Agda surface present")
    if not evidence["cc2_gauge_covariance_evidence"]:
        route_reasons.append("missing CC2 gauge-covariance evidence")

    cc2_flags = extract_flag_rows(scans, ("cc2", "gaugecovariance", "gauge", "covariance", "closed", "proved", "theorem"))
    proof_flags = [
        flag
        for flag in cc2_flags
        if any(word in flag["name"].lower() for word in ("proved", "theorem", "closed", "closure"))
        and any(word in flag["name"].lower() for word in ("gauge", "covariance", "cc2"))
    ]
    if not proof_flags:
        route_reasons.append("no explicit CC2 gauge-covariance theorem/proof/closure flags extracted")
    elif not all(flag["value"] is True for flag in proof_flags):
        route_reasons.append(
            "not all CC2 gauge-covariance theorem flags are true: "
            + ", ".join(sorted({flag["name"] for flag in proof_flags if flag["value"] is not True}))
        )

    if hard_fail_reasons or route_reasons:
        return FAIL_CLOSED, hard_fail_reasons, route_reasons
    return CC2_READY, [], []


def build_summary(repo_root: Path) -> dict[str, Any]:
    surfaces = read_surfaces(repo_root)
    scans = [module_scan(surface) for surface in surfaces]
    evidence = {key: extract_category_evidence(scans, key) for key in EVIDENCE_SPECS}
    decision, hard_fail_reasons, route_reasons = route_decision(scans, evidence)
    summary: dict[str, Any] = {
        "generated_at_utc": datetime.now(timezone.utc).isoformat(),
        "repo_root": repo_root.as_posix(),
        "route_decision": decision,
        "hard_fail_reasons": hard_fail_reasons,
        "route_reasons": route_reasons,
        "fail_reasons": hard_fail_reasons + route_reasons,
        "scanned_surfaces": {
            sprint: [surface.rel_path for surface in surfaces if surface.sprint == sprint]
            for sprint, _ in SURFACE_PATTERNS
        },
        "fail_closed_scan": scans,
        "cc2_gauge_covariance_flags": extract_flag_rows(
            scans, ("cc2", "gaugecovariance", "gauge", "covariance", "closed", "proved", "theorem")
        ),
        "promotion_flags": extract_flag_rows(scans, ("clay", "promotion", "promoted")),
        "blocker_flags": extract_flag_rows(scans, ("blocker", "blocked", "absent", "missing", "false")),
        "status_note": (
            "The audit reads Sprint121 CC1 and available Sprint122 CC2 surfaces when present, plus "
            "current gauge/covariance precursor surfaces. Missing CC2 closure routes fail closed. "
            "Only forbidden markers and true promotion flags cause a nonzero script exit."
        ),
    }
    summary.update(evidence)
    return summary


def render_evidence_section(lines: list[str], title: str, items: list[dict[str, Any]]) -> None:
    lines.extend(["", f"## {title}", ""])
    if not items:
        lines.append("- No matching evidence was extracted.")
        return
    for item in items:
        lines.append(f"### `{item['path']}`")
        for name, value in item.get("strings", {}).items():
            lines.append(f"- `{name}`: `{value}`")
        for name, value in item.get("flags", {}).items():
            lines.append(f"- `{name}`: `{str(value).lower()}`")
        for record in item.get("records", [])[:8]:
            lines.append(f"- Record L{record['line']}: `{record['name']}`")
        if item.get("line_numbers"):
            lines.append(f"- Lines: {', '.join(str(line) for line in item['line_numbers'][:16])}")
        for row in item.get("line_evidence", [])[:6]:
            lines.append(f"- L{row['line']}: `{row['text']}`")
        lines.append("")


def render_flag_section(lines: list[str], title: str, flags: list[dict[str, Any]]) -> None:
    lines.extend(["", f"## {title}", ""])
    if not flags:
        lines.append("- No matching flags were extracted.")
        return
    for flag in flags:
        lines.append(f"- `{flag['name']}` in `{flag['path']}`: `{str(flag['value']).lower()}`")


def render_markdown(summary: dict[str, Any]) -> str:
    lines = [
        "# YM Sprint 122 CC2 Gauge Covariance Audit",
        "",
        f"Route decision: `{summary['route_decision']}`",
        "",
        "## Scanned module surfaces",
        "",
    ]
    for sprint, paths in summary["scanned_surfaces"].items():
        unique_paths = sorted(set(paths))
        if unique_paths:
            for path in unique_paths:
                lines.append(f"- {sprint}: `{path}`")
        else:
            lines.append(f"- {sprint}: no matching Agda modules present")

    for key, spec in EVIDENCE_SPECS.items():
        render_evidence_section(lines, spec["title"], summary[key])

    render_flag_section(lines, "CC2 Gauge Covariance Flags", summary["cc2_gauge_covariance_flags"])
    render_flag_section(lines, "Promotion Flags", summary["promotion_flags"])
    render_flag_section(lines, "Blocker Flags", summary["blocker_flags"])

    lines.extend(["", "## Fail-Closed Reasons", ""])
    if summary["fail_reasons"]:
        for reason in summary["fail_reasons"]:
            lines.append(f"- {reason}")
    else:
        lines.append("- No fail-closed condition was detected.")
    return "\n".join(lines)


def write_outputs(summary: dict[str, Any], out_dir: Path) -> None:
    out_dir.mkdir(parents=True, exist_ok=True)
    (out_dir / SUMMARY_NAME).write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
    (out_dir / REPORT_NAME).write_text(render_markdown(summary) + "\n")


def main() -> None:
    args = parse_args()
    repo_root = args.repo_root.resolve()
    out_dir = args.out_dir if args.out_dir.is_absolute() else repo_root / args.out_dir
    summary = build_summary(repo_root)
    write_outputs(summary, out_dir)
    print(f"wrote {out_dir / SUMMARY_NAME}")
    print(f"wrote {out_dir / REPORT_NAME}")
    print(f"route_decision={summary['route_decision']}")
    for reason in summary["fail_reasons"]:
        print(f"{FAIL_CLOSED}: {reason}")
    if summary["hard_fail_reasons"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
