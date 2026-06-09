#!/usr/bin/env python3
"""Generate the Sprint 126 OS/Symmetry/Group fail-closed audit."""

from __future__ import annotations

import argparse
import json
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable


AUDIT_ID = "ym_sprint126_os_symmetry_group_audit"
DEFAULT_OUT_DIR = Path("outputs/ym_sprint126_os_symmetry_group_audit")
SUMMARY_NAME = f"{AUDIT_ID}_summary.json"
REPORT_NAME = f"{AUDIT_ID}.md"
FAIL_CLOSED = "fail-closed"
PASS_DECISION = "sprint126 os-symmetry-group route ready"
META_CHAR = chr(63)

SURFACE_PATTERNS: tuple[tuple[str, str], ...] = (
    ("sprint105", "DASHI/Physics/Closure/YMSprint105*.agda"),
    ("sprint121", "DASHI/Physics/Closure/YMSprint121*.agda"),
    ("sprint125", "DASHI/Physics/Closure/YMSprint125*.agda"),
    ("sprint126", "DASHI/Physics/Closure/YMSprint126*.agda"),
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

MARKER_PATTERNS: tuple[tuple[str, re.Pattern[str]], ...] = (
    ("incomplete-declaration", re.compile(r"\bpost" + r"ulate\b")),
    ("open-work-marker", re.compile(r"\bTO" + r"DO\b")),
    ("placeholder-marker", re.compile(r"\bst" + r"ub\b", re.IGNORECASE)),
    ("agda-incomplete-braces", re.compile(re.escape("{" + "!") + r"|" + re.escape("!" + "}"))),
    ("rhs-question", re.compile(r"(?m)^\s*[A-Za-z][A-Za-z0-9']*\s*=\s*" + re.escape(META_CHAR) + r"\s*$")),
)

EVIDENCE_SPECS: dict[str, dict[str, Any]] = {
    "os1_evidence": {
        "title": "OS1 Evidence",
        "words": ("os1", "osterwalder", "schrader", "wightman", "reflection", "euclidean"),
        "pattern": r"OS1|Osterwalder|Schrader|Wightman|reflection|Euclidean|OS 1975",
    },
    "sy1_evidence": {
        "title": "SY1 Evidence",
        "words": ("sy1", "symmetry", "restoration", "poincare", "covariance", "spectrum"),
        "pattern": r"SY1|symmetry|restoration|Poincare|covariance|spectrum|SO4|Lorentz",
    },
    "gg1_evidence": {
        "title": "GG1 Evidence",
        "words": ("gg1", "group", "compact", "simple", "gauge", "lie", "parameter"),
        "pattern": r"GG1|compact|simple|group|gauge|Lie|parameter",
    },
    "sc1_evidence": {
        "title": "SC1 Evidence",
        "words": ("sc1", "log", "generator", "functional", "calculus", "spectral"),
        "pattern": r"SC1|log[- ]?generator|functional|calculus|spectral",
    },
    "sc2_evidence": {
        "title": "SC2 Evidence",
        "words": ("sc2", "spectral", "transport", "gap", "threshold", "continuum"),
        "pattern": r"SC2|spectral[- ]?transport|gap|threshold|continuum",
    },
    "sc3_evidence": {
        "title": "SC3 Evidence",
        "words": ("sc3", "transfer", "lower", "bound", "coercivity", "mass"),
        "pattern": r"SC3|transfer|lower|bound|coercivity|mass",
    },
}

CLOSURE_REQUIREMENTS: dict[str, tuple[str, ...]] = {
    "OS1": ("os1", "osterwalder", "schrader", "wightman", "reflection"),
    "SY1": ("sy1", "symmetry", "restoration", "poincare", "covariance", "spectrum"),
    "GG1": ("gg1", "group", "compact", "simple", "gauge"),
    "SC1": ("sc1", "log", "generator", "functional", "calculus"),
    "SC2": ("sc2", "spectral", "transport", "gap"),
    "SC3": ("sc3", "transfer", "lower", "bound"),
}
CLOSURE_WORDS = ("closed", "proved", "proof", "theorem", "ready", "discharged")


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


def closure_status(scans: list[dict[str, Any]]) -> dict[str, dict[str, Any]]:
    closure_needles = tuple(normalize(word) for word in CLOSURE_WORDS)
    status: dict[str, dict[str, Any]] = {}
    for route, words in CLOSURE_REQUIREMENTS.items():
        route_needles = tuple(normalize(word) for word in words)
        flags: list[dict[str, Any]] = []
        references: list[dict[str, Any]] = []
        for scan in scans:
            for name, value in scan["bool_assignments"].items():
                normalized = normalize(name)
                route_hit = route.lower() in normalized or any(needle in normalized for needle in route_needles)
                closure_hit = any(needle in normalized for needle in closure_needles)
                if route_hit and closure_hit:
                    flags.append({"path": scan["path"], "group": scan["group"], "name": name, "value": value})
            for name, expr in scan["bool_references"].items():
                normalized = normalize(name)
                route_hit = route.lower() in normalized or any(needle in normalized for needle in route_needles)
                closure_hit = any(needle in normalized for needle in closure_needles)
                if route_hit and closure_hit:
                    references.append({"path": scan["path"], "group": scan["group"], "name": name, "expression": expr})
        status[route] = {
            "flags": flags,
            "references": references,
            "closed": bool(flags) and all(flag["value"] is True for flag in flags),
            "false_flags": [flag for flag in flags if flag["value"] is not True],
        }
    return status


def route_decision(
    scans: list[dict[str, Any]],
    evidence: dict[str, list[dict[str, Any]]],
    closures: dict[str, dict[str, Any]],
) -> tuple[str, list[str], list[str]]:
    hard_fail_reasons: list[str] = []
    route_reasons: list[str] = []

    groups_present = {scan["group"] for scan in scans}
    for group, _pattern in SURFACE_PATTERNS:
        if group not in groups_present:
            route_reasons.append(f"missing required surface group: {group}")

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

    for route in ("OS1", "SY1", "GG1"):
        if not closures[route]["flags"]:
            route_reasons.append(f"no explicit {route} closure/proof flags extracted")
        elif not closures[route]["closed"]:
            false_names = ", ".join(sorted({flag["name"] for flag in closures[route]["false_flags"]}))
            route_reasons.append(f"{route} closure flags are not all true: {false_names}")

    for route in ("SC1", "SC2", "SC3"):
        if not closures[route]["flags"]:
            route_reasons.append(f"no explicit hard upstream {route} gate flags extracted")
        elif not closures[route]["closed"]:
            false_names = ", ".join(sorted({flag["name"] for flag in closures[route]["false_flags"]}))
            route_reasons.append(f"hard upstream {route} gate is not closed: {false_names}")

    if hard_fail_reasons or route_reasons:
        return FAIL_CLOSED, hard_fail_reasons, route_reasons
    return PASS_DECISION, [], []


def build_summary(repo_root: Path) -> dict[str, Any]:
    surfaces = read_surfaces(repo_root)
    scans = [module_scan(surface) for surface in surfaces]
    evidence = {key: extract_category_evidence(scans, key) for key in EVIDENCE_SPECS}
    closures = closure_status(scans)
    decision, hard_fail_reasons, route_reasons = route_decision(scans, evidence, closures)
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
        "closure_flags": closures,
        "os1_closure_flags": closures["OS1"]["flags"],
        "sy1_closure_flags": closures["SY1"]["flags"],
        "gg1_closure_flags": closures["GG1"]["flags"],
        "hard_upstream_gate_flags": {
            route: closures[route]
            for route in ("SC1", "SC2", "SC3")
        },
        "os_symmetry_group_flags_closed": all(closures[route]["closed"] for route in ("OS1", "SY1", "GG1")),
        "hard_upstream_gates_closed": all(closures[route]["closed"] for route in ("SC1", "SC2", "SC3")),
        "clay_promotion_flags": extract_flag_rows(scans, ("clayYangMillsPromoted",)),
        "status_note": (
            "The audit reads Sprint105, Sprint121, Sprint125, and Sprint126 Closure Agda surfaces. "
            "It rejects any direct true assignment to clayYangMillsPromoted and keeps the route fail-closed "
            "unless OS1, SY1, GG1, SC1, SC2, and SC3 closure/proof flags are directly present and true."
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


def render_closure_section(lines: list[str], title: str, status: dict[str, Any]) -> None:
    lines.extend(["", f"## {title}", ""])
    lines.append(f"- Closed: `{str(status['closed']).lower()}`")
    if not status["flags"]:
        lines.append("- No direct closure flags were extracted.")
    for flag in status["flags"]:
        lines.append(f"- Direct `{flag['name']}` in `{flag['path']}`: `{str(flag['value']).lower()}`")
    for ref in status["references"]:
        lines.append(f"- Reference `{ref['name']}` in `{ref['path']}`: `{ref['expression']}`")


def render_markdown(summary: dict[str, Any]) -> str:
    lines = [
        "# YM Sprint 126 OS/Symmetry/Group Audit",
        "",
        f"Route decision: `{summary['route_decision']}`",
        "OS1/SY1/GG1 closure flags closed: "
        f"`{str(summary['os_symmetry_group_flags_closed']).lower()}`",
        "Hard upstream SC1/SC2/SC3 gates closed: "
        f"`{str(summary['hard_upstream_gates_closed']).lower()}`",
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

    for key, spec in EVIDENCE_SPECS.items():
        render_evidence_section(lines, spec["title"], summary[key])

    for route in ("OS1", "SY1", "GG1", "SC1", "SC2", "SC3"):
        render_closure_section(lines, f"{route} Closure Flags", summary["closure_flags"][route])

    render_flag_rows(lines, "Clay Promotion Flags", summary["clay_promotion_flags"])

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
