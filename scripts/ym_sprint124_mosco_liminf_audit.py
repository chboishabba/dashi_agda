#!/usr/bin/env python3
"""Generate the Sprint 124 MC1 Mosco liminf audit from Agda evidence text."""

from __future__ import annotations

import argparse
import json
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable


DEFAULT_OUT_DIR = Path("outputs/ym_sprint124_mosco_liminf_audit")
SUMMARY_NAME = "ym_sprint124_mosco_liminf_audit_summary.json"
REPORT_NAME = "ym_sprint124_mosco_liminf_audit.md"

SURFACE_PATTERNS: tuple[tuple[str, str], ...] = (
    ("sprint121_cc1", "DASHI/Physics/Closure/YMSprint121*.agda"),
    ("sprint122_carrier", "DASHI/Physics/Closure/YMSprint122*.agda"),
    ("sprint123_wc_mc", "DASHI/Physics/Closure/YMSprint123*.agda"),
    ("sprint124_mc1", "DASHI/Physics/Closure/YMSprint124*.agda"),
)

FAIL_CLOSED = "fail-closed"
MC1_READY = "sprint124 mc1 mosco liminf route proved"
META_CHAR = chr(63)

BOOL_PATTERN = re.compile(r"^([A-Za-z][A-Za-z0-9']*)\s*=\s*(true|false)\s*$", re.MULTILINE)
STRING_PATTERN = re.compile(
    r"^([A-Za-z][A-Za-z0-9']*)\s*:\s*String\s*\n"
    r"\1\s*=\s*(?:\n\s*)?\"([^\"]*)\"",
    re.MULTILINE,
)
RECORD_PATTERN = re.compile(r"^\s*record\s+([A-Za-z][A-Za-z0-9']*)\s*:\s*Set\w*\b", re.MULTILINE)
DATA_HEADER_PATTERN = re.compile(r"^data\s+\S+.*\bwhere\s*$")
PROMOTION_TRUE_PATTERN = re.compile(r"\b[A-Za-z][A-Za-z0-9']*(?:Promotion|Promoted)\s*=\s*true\b")

MARKER_PATTERNS: tuple[tuple[str, re.Pattern[str]], ...] = (
    ("incomplete-declaration", re.compile(r"\bpost" + r"ulate\b")),
    ("incomplete-note", re.compile(r"\bTO" + r"DO\b")),
    ("incomplete-token", re.compile(r"\bstu" + r"b\b", re.IGNORECASE)),
    ("agda-meta-gap", re.compile(re.escape("{" + "!") + r"|" + re.escape("!" + "}"))),
    ("rhs-unresolved", re.compile(r"(?m)^\s*[A-Za-z][A-Za-z0-9']*\s*=\s*" + re.escape(META_CHAR) + r"\s*$")),
    ("type-unresolved", re.compile(r"(?m)^\s*[A-Za-z][A-Za-z0-9']*\s*:\s*" + re.escape(META_CHAR) + r"\s*$")),
)

EVIDENCE_SPECS: dict[str, dict[str, Any]] = {
    "mc1_mosco_liminf_evidence": {
        "title": "MC1 Mosco Liminf Evidence",
        "words": (
            "mc1",
            "mosco",
            "liminf",
            "lower",
            "semicontinuity",
            "lsc",
            "closed",
            "form",
            "energy",
        ),
        "pattern": r"mc1|mosco|liminf|lower|semicontinuity|lsc|closed form|energy",
    },
    "cc1_route_evidence": {
        "title": "CC1 Route Evidence",
        "words": ("cc1", "common", "carrier", "kernel", "embedding", "projection", "quotient"),
        "pattern": r"cc1|common|carrier|kernel|embedding|projection|quotient|E_a|P_a",
    },
    "wc1_route_evidence": {
        "title": "WC1 Route Evidence",
        "words": ("wc1", "weak", "compact", "compactness", "subsequence", "tight", "limit"),
        "pattern": r"wc1|weak|compact|compactness|subsequence|tight|limit",
    },
    "mc3_route_evidence": {
        "title": "MC3 Route Evidence",
        "words": ("mc3", "uniform", "form", "lower", "bound", "quadratic", "coercivity"),
        "pattern": r"mc3|uniform|form|lower|bound|quadratic|coercivity",
    },
    "manuscript_evidence": {
        "title": "Manuscript Evidence",
        "words": ("manuscript", "citation", "proposition", "dependencies", "obligations", "lower-bound"),
        "pattern": r"manuscript|citation|proposition|dependencies|obligations|lower[- ]?bound",
    },
    "route_evidence": {
        "title": "Route Evidence",
        "words": ("route", "decision", "dependencies", "proof", "obligations", "fail", "closed"),
        "pattern": r"route|decision|dependencies|proof|obligations|fail[- ]?closed",
    },
    "blocker_evidence": {
        "title": "Blocker Evidence",
        "words": ("blocked", "blocker", "false", "missing", "absent", "fail", "unproved"),
        "pattern": r"blocked|blocker|false|missing|absent|fail[- ]?closed|unproved|not proved|remain[s]? false",
    },
}

ROUTE_REQUIREMENTS: dict[str, tuple[str, ...]] = {
    "MC1": ("mc1", "mosco", "liminf"),
    "CC1": ("cc1", "commoncarrier", "common", "carrier"),
    "WC1": ("wc1", "weakcompactness", "weak", "compactness"),
    "MC3": ("mc3", "uniformform", "quadraticform", "coercivity"),
}
ROUTE_CLOSURE_WORDS = (
    "proved",
    "proof",
    "theorem",
    "closed",
    "closure",
    "ready",
    "discharged",
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


def marker_hits(text: str) -> list[dict[str, Any]]:
    hits: list[dict[str, Any]] = []
    for name, pattern in MARKER_PATTERNS:
        for match in pattern.finditer(text):
            hits.append({"marker": name, "line": text.count("\n", 0, match.start()) + 1})
    return hits


def module_scan(surface: ModuleSurface) -> dict[str, Any]:
    scan: dict[str, Any] = {
        "path": surface.rel_path,
        "group": surface.group,
        "bool_assignments": bool_assignments(surface.text),
        "string_assignments": string_assignments(surface.text),
        "record_declarations": record_declarations(surface.text),
        "empty_data_declarations": empty_data_declarations(surface.text),
        "marker_hits": marker_hits(surface.text),
        "promotion_true_detected": bool(PROMOTION_TRUE_PATTERN.search(surface.text)),
    }
    scan["evidence_lines"] = {
        key: source_lines(surface.text, spec["pattern"], limit=18)
        for key, spec in EVIDENCE_SPECS.items()
    }
    return scan


def normalize_name(value: str) -> str:
    return value.lower().replace("_", "").replace("-", "").replace(" ", "")


def selected_strings(scan: dict[str, Any], words: Iterable[str]) -> dict[str, str]:
    needles = tuple(word.lower() for word in words)
    return {
        name: value
        for name, value in scan["string_assignments"].items()
        if any(needle in f"{name} {value}".lower() for needle in needles)
    }


def selected_flags(scan: dict[str, Any], words: Iterable[str]) -> dict[str, bool]:
    needles = tuple(normalize_name(word) for word in words)
    selected: dict[str, bool] = {}
    for name, value in scan["bool_assignments"].items():
        normalized = normalize_name(name)
        if "promotion" in normalized and "promoted" not in normalized and "clay" not in normalized:
            continue
        if any(needle in normalized for needle in needles):
            selected[name] = value
    return selected


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
    needles = tuple(normalize_name(word) for word in words)
    for scan in scans:
        for name, value in scan["bool_assignments"].items():
            normalized = normalize_name(name)
            if "promotion" in normalized and "promoted" not in normalized and "clay" not in normalized:
                continue
            if any(needle in normalized for needle in needles):
                rows.append({"path": scan["path"], "group": scan["group"], "name": name, "value": value})
    return rows


def route_flag_rows(scans: list[dict[str, Any]], route: str, words: Iterable[str]) -> list[dict[str, Any]]:
    needles = tuple(normalize_name(word) for word in words)
    closure_needles = tuple(normalize_name(word) for word in ROUTE_CLOSURE_WORDS)
    rows: list[dict[str, Any]] = []
    for scan in scans:
        for name, value in scan["bool_assignments"].items():
            normalized = normalize_name(name)
            route_hit = route.lower() in normalized or any(needle in normalized for needle in needles)
            closure_hit = any(needle in normalized for needle in closure_needles)
            if route_hit and closure_hit:
                rows.append({"path": scan["path"], "group": scan["group"], "name": name, "value": value})
    return rows


def route_status(scans: list[dict[str, Any]]) -> dict[str, dict[str, Any]]:
    status: dict[str, dict[str, Any]] = {}
    for route, words in ROUTE_REQUIREMENTS.items():
        flags = route_flag_rows(scans, route, words)
        status[route] = {
            "flags": flags,
            "closed": bool(flags) and all(flag["value"] is True for flag in flags),
            "false_flags": [flag for flag in flags if flag["value"] is not True],
        }
    return status


def route_decision(
    scans: list[dict[str, Any]],
    evidence: dict[str, list[dict[str, Any]]],
    routes: dict[str, dict[str, Any]],
) -> tuple[str, list[str], list[str]]:
    hard_fail_reasons: list[str] = []
    route_reasons: list[str] = []

    groups_present = {scan["group"] for scan in scans}
    for group, _pattern in SURFACE_PATTERNS:
        if group not in groups_present:
            route_reasons.append(f"missing required surface group: {group}")

    for scan in scans:
        if scan["promotion_true_detected"]:
            hard_fail_reasons.append(f"{scan['path']}: promotion flag set true")
        if scan["empty_data_declarations"]:
            hard_fail_reasons.append(f"{scan['path']}: empty data declaration present")
        if scan["marker_hits"]:
            details = ", ".join(f"{hit['marker']}@L{hit['line']}" for hit in scan["marker_hits"][:12])
            hard_fail_reasons.append(f"{scan['path']}: incomplete production marker present ({details})")

    for key, spec in EVIDENCE_SPECS.items():
        if key != "blocker_evidence" and not evidence[key]:
            route_reasons.append(f"missing evidence category: {spec['title']}")

    for route in ("MC1", "CC1", "WC1", "MC3"):
        route_flags = routes[route]["flags"]
        false_flags = routes[route]["false_flags"]
        if not route_flags:
            route_reasons.append(f"no explicit {route} closure/proof route flags extracted")
        elif false_flags:
            route_reasons.append(
                f"{route} route flags are not all true: "
                + ", ".join(sorted({flag["name"] for flag in false_flags}))
            )

    if hard_fail_reasons or route_reasons:
        return FAIL_CLOSED, hard_fail_reasons, route_reasons
    return MC1_READY, [], []


def build_summary(repo_root: Path) -> dict[str, Any]:
    surfaces = read_surfaces(repo_root)
    scans = [module_scan(surface) for surface in surfaces]
    evidence = {key: extract_category_evidence(scans, key) for key in EVIDENCE_SPECS}
    routes = route_status(scans)
    decision, hard_fail_reasons, route_reasons = route_decision(scans, evidence, routes)
    summary: dict[str, Any] = {
        "audit_id": "ym_sprint124_mosco_liminf_audit",
        "route_decision": decision,
        "hard_fail_reasons": hard_fail_reasons,
        "route_reasons": route_reasons,
        "fail_reasons": hard_fail_reasons + route_reasons,
        "scanned_surfaces": {
            group: [surface.rel_path for surface in surfaces if surface.group == group]
            for group, _pattern in SURFACE_PATTERNS
        },
        "fail_closed_scan": scans,
        "route_closure_flags": routes,
        "mc1_route_flags": routes["MC1"]["flags"],
        "cc1_route_flags": routes["CC1"]["flags"],
        "wc1_route_flags": routes["WC1"]["flags"],
        "mc3_route_flags": routes["MC3"]["flags"],
        "all_route_flags_closed": all(routes[route]["closed"] for route in ("MC1", "CC1", "WC1", "MC3")),
        "promotion_flags": extract_flag_rows(scans, ("clay", "promoted")),
        "blocker_flags": extract_flag_rows(scans, ("blocker", "blocked", "absent", "missing", "false")),
        "status_note": (
            "The audit reads Sprint121 through Sprint124 Closure Agda surfaces and accepts only when "
            "MC1, CC1, WC1, and MC3 closure/proof route flags are present and true. Missing route "
            "evidence, false route flags, true promotion flags, empty data declarations, or incomplete "
            "production markers keep the decision fail-closed."
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
            lines.append(f"- Lines: {', '.join(str(line) for line in item['line_numbers'][:18])}")
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
        "# YM Sprint 124 MC1 Mosco Liminf Audit",
        "",
        f"Route decision: `{summary['route_decision']}`",
        f"All MC1/CC1/WC1/MC3 route flags closed: `{str(summary['all_route_flags_closed']).lower()}`",
        "",
        "## Scanned Module Surfaces",
        "",
    ]
    for group, paths in summary["scanned_surfaces"].items():
        unique_paths = sorted(set(paths))
        if unique_paths:
            for path in unique_paths:
                lines.append(f"- {group}: `{path}`")
        else:
            lines.append(f"- {group}: no matching Agda modules present")

    for key, spec in EVIDENCE_SPECS.items():
        render_evidence_section(lines, spec["title"], summary[key])

    for route in ("MC1", "CC1", "WC1", "MC3"):
        render_flag_section(lines, f"{route} Route Closure Flags", summary["route_closure_flags"][route]["flags"])

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
