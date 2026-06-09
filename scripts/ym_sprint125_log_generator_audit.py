#!/usr/bin/env python3
"""Generate the Sprint 125 log-generator dependency audit."""

from __future__ import annotations

import argparse
import json
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable


AUDIT_ID = "ym_sprint125_log_generator_audit"
DEFAULT_OUT_DIR = Path("outputs/ym_sprint125_log_generator_audit")
SUMMARY_NAME = f"{AUDIT_ID}_summary.json"
REPORT_NAME = f"{AUDIT_ID}.md"
FAIL_CLOSED = "fail-closed"
PASS_DECISION = "sprint125 log-generator route ready"

SURFACE_PATTERNS: tuple[tuple[str, str], ...] = (
    ("sprint108", "DASHI/Physics/Closure/YMSprint108*.agda"),
    ("sprint120", "DASHI/Physics/Closure/YMSprint120*.agda"),
    ("sprint124", "DASHI/Physics/Closure/YMSprint124*.agda"),
    ("sprint125", "DASHI/Physics/Closure/YMSprint125*.agda"),
)

BOOL_PATTERN = re.compile(r"^([A-Za-z][A-Za-z0-9']*)\s*=\s*(true|false)\s*$", re.MULTILINE)
BOOL_REF_PATTERN = re.compile(
    r"^([A-Za-z][A-Za-z0-9']*)\s*:\s*Bool\s*\n"
    r"\1\s*=\s*(?:\n\s*)?([A-Za-z][A-Za-z0-9'.]*)\s*$",
    re.MULTILINE,
)
STRING_PATTERN = re.compile(
    r"^([A-Za-z][A-Za-z0-9']*)\s*:\s*String\s*\n"
    r"\1\s*=\s*(?:\n\s*)?\"([^\"]*)\"",
    re.MULTILINE,
)
RECORD_PATTERN = re.compile(r"^\s*record\s+([A-Za-z][A-Za-z0-9']*)\s*:\s*Set\w*\b", re.MULTILINE)
DATA_HEADER_PATTERN = re.compile(r"^data\s+\S+.*\bwhere\s*$")
CLAY_PROMOTED_TRUE_PATTERN = re.compile(r"(?m)^clayYangMillsPromoted\s*=\s*true\s*$")
META_CHAR = chr(63)

MARKER_PATTERNS: tuple[tuple[str, re.Pattern[str]], ...] = (
    ("incomplete-declaration", re.compile(r"\bpost" + r"ulate\b")),
    ("todo-marker", re.compile(r"\bTO" + r"DO\b")),
    ("placeholder-marker", re.compile(r"\bst" + r"ub\b", re.IGNORECASE)),
    ("agda-hole", re.compile(re.escape("{" + "!") + r"|" + re.escape("!" + "}"))),
    ("rhs-question", re.compile(r"(?m)^\s*[A-Za-z][A-Za-z0-9']*\s*=\s*" + re.escape(META_CHAR) + r"\s*$")),
)

EVIDENCE_SPECS: dict[str, dict[str, Any]] = {
    "sc1_evidence": {
        "title": "SC1 Evidence",
        "words": (
            "sc1",
            "functional",
            "calculus",
            "log",
            "generator",
            "common",
            "core",
            "spectral",
            "mapping",
            "normalization",
        ),
        "pattern": r"SC1|functional|calculus|log[- ]?generator|common[- ]?core|spectral[- ]?mapping|normalization",
    },
    "sc2_evidence": {
        "title": "SC2 Evidence",
        "words": ("sc2", "spectral", "transport", "threshold", "excited", "continuum"),
        "pattern": r"SC2|spectral|transport|threshold|excited|continuum",
    },
    "sc3_evidence": {
        "title": "SC3 Evidence",
        "words": ("sc3", "uniform", "form", "lower", "coercivity", "bound"),
        "pattern": r"SC3|uniform|form|lower|coercivity|bound",
    },
    "log_generator_evidence": {
        "title": "Log-Generator Evidence",
        "words": ("log", "generator", "functional", "calculus", "mapping", "core", "normalization"),
        "pattern": r"log[- ]?generator|functional|calculus|mapping|common[- ]?core|normalization",
    },
    "spectral_transport_evidence": {
        "title": "Spectral-Transport Evidence",
        "words": ("spectral", "transport", "gap", "threshold", "excited"),
        "pattern": r"spectral[- ]?transport|spectral|transport|gap|threshold|excited",
    },
}

REQUIRED_SC1_FLAGS: tuple[str, ...] = (
    "functionalCalculusTheoremProvedHere",
    "spectralMappingMonotonicityProvedHere",
    "domainCommonCoreConstructedHere",
    "normalizationContinuumLimitProvedHere",
    "finiteGapConvertedToPhysicalEnergyGapHere",
    "physicalHamiltonianTheoremLocallyClosed",
    "logGeneratorCalculusClosedHere",
)


@dataclass(frozen=True)
class ModuleSurface:
    path: Path
    rel_path: str
    group: str
    text: str


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--out-dir", type=Path, default=DEFAULT_OUT_DIR)
    return parser.parse_args()


def read_surfaces(repo_root: Path) -> list[ModuleSurface]:
    seen: set[Path] = set()
    surfaces: list[ModuleSurface] = []
    for group, pattern in SURFACE_PATTERNS:
        for path in sorted(repo_root.glob(pattern)):
            if not path.is_file() or path in seen:
                continue
            seen.add(path)
            surfaces.append(ModuleSurface(path, path.relative_to(repo_root).as_posix(), group, path.read_text()))
    return surfaces


def line_number(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def bool_assignments(text: str) -> dict[str, bool]:
    return {name: value == "true" for name, value in BOOL_PATTERN.findall(text)}


def bool_references(text: str) -> dict[str, str]:
    return {
        name: expr
        for name, expr in BOOL_REF_PATTERN.findall(text)
        if expr not in ("true", "false")
    }


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


def record_declarations(text: str) -> list[dict[str, Any]]:
    return [
        {"line": line_number(text, match.start()), "name": match.group(1), "text": match.group(0).strip()}
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


def marker_hits(text: str) -> list[dict[str, Any]]:
    hits: list[dict[str, Any]] = []
    for name, pattern in MARKER_PATTERNS:
        for match in pattern.finditer(text):
            hits.append({"marker": name, "line": line_number(text, match.start())})
    return hits


def module_scan(surface: ModuleSurface) -> dict[str, Any]:
    scan: dict[str, Any] = {
        "path": surface.rel_path,
        "group": surface.group,
        "bool_assignments": bool_assignments(surface.text),
        "bool_references": bool_references(surface.text),
        "string_assignments": string_assignments(surface.text),
        "record_declarations": record_declarations(surface.text),
        "empty_data_declarations": empty_data_declarations(surface.text),
        "marker_hits": marker_hits(surface.text),
        "clay_promotion_true_detected": bool(CLAY_PROMOTED_TRUE_PATTERN.search(surface.text)),
    }
    scan["evidence_lines"] = {
        key: source_lines(surface.text, spec["pattern"], limit=20)
        for key, spec in EVIDENCE_SPECS.items()
    }
    return scan


def normalize(value: str) -> str:
    return value.lower().replace("_", "").replace("-", "").replace(" ", "")


def selected_strings(scan: dict[str, Any], words: Iterable[str]) -> dict[str, str]:
    needles = tuple(word.lower() for word in words)
    return {
        name: value
        for name, value in scan["string_assignments"].items()
        if any(needle in f"{name} {value}".lower() for needle in needles)
    }


def selected_flags(scan: dict[str, Any], words: Iterable[str]) -> dict[str, bool]:
    needles = tuple(normalize(word) for word in words)
    return {
        name: value
        for name, value in scan["bool_assignments"].items()
        if any(needle in normalize(name) for needle in needles)
    }


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
                    "group": scan["group"],
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
    needles = tuple(normalize(word) for word in words)
    for scan in scans:
        for name, value in scan["bool_assignments"].items():
            if any(needle in normalize(name) for needle in needles):
                rows.append({"path": scan["path"], "group": scan["group"], "name": name, "value": value})
    return rows


def required_sc1_dependency_flags(scans: list[dict[str, Any]]) -> dict[str, dict[str, Any]]:
    rows: dict[str, dict[str, Any]] = {}
    for required in REQUIRED_SC1_FLAGS:
        matches: list[dict[str, Any]] = []
        references: list[dict[str, Any]] = []
        for scan in scans:
            if required in scan["bool_assignments"]:
                matches.append(
                    {
                        "path": scan["path"],
                        "group": scan["group"],
                        "name": required,
                        "value": scan["bool_assignments"][required],
                    }
                )
            if required in scan["bool_references"]:
                references.append(
                    {
                        "path": scan["path"],
                        "group": scan["group"],
                        "name": required,
                        "expression": scan["bool_references"][required],
                    }
                )
        rows[required] = {
            "matches": matches,
            "references": references,
            "present": bool(matches),
            "all_true": bool(matches) and all(match["value"] is True for match in matches),
            "false_matches": [match for match in matches if match["value"] is not True],
        }
    return rows


def route_decision(
    scans: list[dict[str, Any]],
    evidence: dict[str, list[dict[str, Any]]],
    required_flags: dict[str, dict[str, Any]],
) -> tuple[str, list[str], list[str]]:
    hard_fail_reasons: list[str] = []
    route_reasons: list[str] = []

    groups_present = {scan["group"] for scan in scans}
    for group, _pattern in SURFACE_PATTERNS:
        if group != "sprint125" and group not in groups_present:
            route_reasons.append(f"missing required surface group: {group}")
    if "sprint125" not in groups_present:
        route_reasons.append("missing Sprint125 Agda surface group")

    for scan in scans:
        if scan["clay_promotion_true_detected"]:
            hard_fail_reasons.append(f"{scan['path']}: clayYangMillsPromoted is true")
        if scan["empty_data_declarations"]:
            hard_fail_reasons.append(f"{scan['path']}: empty data declaration present")
        if scan["marker_hits"]:
            details = ", ".join(f"{hit['marker']}@L{hit['line']}" for hit in scan["marker_hits"][:12])
            hard_fail_reasons.append(f"{scan['path']}: incomplete marker present ({details})")

    for key, spec in EVIDENCE_SPECS.items():
        if not evidence[key]:
            route_reasons.append(f"missing evidence category: {spec['title']}")

    for name, status in required_flags.items():
        if not status["present"]:
            route_reasons.append(f"missing required SC1 dependency flag: {name}")
        elif not status["all_true"]:
            false_paths = ", ".join(f"{row['path']}={str(row['value']).lower()}" for row in status["false_matches"])
            route_reasons.append(f"required SC1 dependency flag is not true: {name} ({false_paths})")

    if hard_fail_reasons or route_reasons:
        return FAIL_CLOSED, hard_fail_reasons, route_reasons
    return PASS_DECISION, [], []


def build_summary(repo_root: Path) -> dict[str, Any]:
    surfaces = read_surfaces(repo_root)
    scans = [module_scan(surface) for surface in surfaces]
    evidence = {key: extract_category_evidence(scans, key) for key in EVIDENCE_SPECS}
    required_flags = required_sc1_dependency_flags(scans)
    decision, hard_fail_reasons, route_reasons = route_decision(scans, evidence, required_flags)
    summary: dict[str, Any] = {
        "audit_id": AUDIT_ID,
        "route_decision": decision,
        "hard_fail_reasons": hard_fail_reasons,
        "route_reasons": route_reasons,
        "fail_reasons": hard_fail_reasons + route_reasons,
        "scanned_surfaces": {
            group: [surface.rel_path for surface in surfaces if surface.group == group]
            for group, _pattern in SURFACE_PATTERNS
        },
        "fail_closed_scan": scans,
        "required_sc1_dependency_flags": required_flags,
        "all_required_sc1_dependency_flags_true": all(
            status["all_true"] for status in required_flags.values()
        ),
        "clay_promotion_flags": extract_flag_rows(scans, ("clayYangMillsPromoted",)),
        "log_generator_flags": extract_flag_rows(scans, ("log", "generator", "functional", "calculus")),
        "spectral_transport_flags": extract_flag_rows(scans, ("spectral", "transport", "gap", "threshold")),
        "status_note": (
            "The audit reads Sprint108, Sprint120, Sprint124, and Sprint125 Closure Agda surfaces. "
            "It rejects any direct true assignment to clayYangMillsPromoted and keeps the route fail-closed "
            "unless every required SC1 dependency flag is directly present and true."
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
            lines.append(f"- Lines: {', '.join(str(line) for line in item['line_numbers'][:20])}")
        for row in item.get("line_evidence", [])[:6]:
            lines.append(f"- L{row['line']}: `{row['text']}`")
        lines.append("")


def render_flag_rows(lines: list[str], title: str, flags: list[dict[str, Any]]) -> None:
    lines.extend(["", f"## {title}", ""])
    if not flags:
        lines.append("- No matching flags were extracted.")
        return
    for flag in flags:
        lines.append(f"- `{flag['name']}` in `{flag['path']}`: `{str(flag['value']).lower()}`")


def render_markdown(summary: dict[str, Any]) -> str:
    lines = [
        "# YM Sprint 125 Log-Generator Audit",
        "",
        f"Route decision: `{summary['route_decision']}`",
        "All required SC1 dependency flags true: "
        f"`{str(summary['all_required_sc1_dependency_flags_true']).lower()}`",
        "",
        "## Scanned Module Surfaces",
        "",
    ]
    for group, paths in summary["scanned_surfaces"].items():
        if paths:
            for path in sorted(set(paths)):
                lines.append(f"- {group}: `{path}`")
        else:
            lines.append(f"- {group}: no matching Agda modules present")

    lines.extend(["", "## Required SC1 Dependency Flags", ""])
    for name, status in summary["required_sc1_dependency_flags"].items():
        flag_status = "true" if status["all_true"] else "false"
        lines.append(f"- `{name}`: `{flag_status}`")
        for match in status["matches"]:
            lines.append(f"  - direct `{match['path']}`: `{str(match['value']).lower()}`")
        for ref in status["references"]:
            lines.append(f"  - reference `{ref['path']}`: `{ref['expression']}`")

    for key, spec in EVIDENCE_SPECS.items():
        render_evidence_section(lines, spec["title"], summary[key])

    render_flag_rows(lines, "Clay Promotion Flags", summary["clay_promotion_flags"])
    render_flag_rows(lines, "Log-Generator Flags", summary["log_generator_flags"])
    render_flag_rows(lines, "Spectral-Transport Flags", summary["spectral_transport_flags"])

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
