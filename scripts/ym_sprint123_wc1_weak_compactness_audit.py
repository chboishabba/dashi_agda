#!/usr/bin/env python3
"""Generate the Sprint 123 WC1 weak compactness extraction audit."""

from __future__ import annotations

import argparse
import json
import re
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Iterable


DEFAULT_OUT_DIR = Path("outputs/ym_sprint123_wc1_weak_compactness_audit")
SUMMARY_NAME = "ym_sprint123_wc1_weak_compactness_audit_summary.json"
REPORT_NAME = "ym_sprint123_wc1_weak_compactness_audit.md"

SURFACE_PATTERNS: tuple[tuple[str, str], ...] = (
    ("sprint121_cc1", "DASHI/Physics/Closure/YMSprint121*.agda"),
    ("sprint122_carrier", "DASHI/Physics/Closure/YMSprint122*.agda"),
    ("sprint123_wc1", "DASHI/Physics/Closure/YMSprint123*.agda"),
)

FAIL_CLOSED = "fail-closed"
WC1_CLOSED = "sprint123 wc1 weak compactness extraction closed"
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
    ("post" + "ulate", re.compile(r"\bpost" + r"ulate\b")),
    ("TO" + "DO", re.compile(r"\bTO" + r"DO\b")),
    ("stu" + "b", re.compile(r"\bstu" + r"b\b", re.IGNORECASE)),
    ("for" + "bidden", re.compile(r"\bfor" + r"bidden\b", re.IGNORECASE)),
    ("agda-meta-gap", re.compile(re.escape("{" + "!") + r"|" + re.escape("!" + "}"))),
    ("rhs-unresolved", re.compile(r"(?m)^\s*[A-Za-z][A-Za-z0-9']*\s*=\s*" + re.escape(META_CHAR) + r"\s*$")),
    ("type-unresolved", re.compile(r"(?m)^\s*[A-Za-z][A-Za-z0-9']*\s*:\s*" + re.escape(META_CHAR) + r"\s*$")),
)

EVIDENCE_SPECS: dict[str, dict[str, Any]] = {
    "cc1_evidence": {
        "title": "Sprint121 CC1 Evidence",
        "words": ("cc1", "common", "carrier", "kernel", "embedding", "projection", "quotient"),
        "pattern": r"cc1|common|carrier|kernel|embedding|projection|quotient|H_cc1|E_a|P_a",
    },
    "sprint122_carrier_evidence": {
        "title": "Sprint122 Carrier Evidence",
        "words": (
            "cc2",
            "cc3",
            "cc4",
            "carrier",
            "gauge",
            "norm",
            "window",
            "residual",
            "covariance",
            "approximate",
        ),
        "pattern": r"cc2|cc3|cc4|carrier|gauge|norm|window|residual|covariance|approximate|uniform",
    },
    "wc1_extraction_evidence": {
        "title": "Sprint123 WC1 Extraction Evidence",
        "words": (
            "wc1",
            "weak",
            "compact",
            "compactness",
            "extraction",
            "subsequence",
            "bounded",
            "energy",
            "tight",
            "sector",
            "null",
            "mosco",
        ),
        "pattern": r"wc1|weak|compact|compactness|extraction|subsequence|bounded|energy|tight|sector|null|mosco",
    },
    "blocker_evidence": {
        "title": "Blocker Evidence",
        "words": ("blocked", "blocker", "false", "missing", "absent", "fail", "closed", "unproved"),
        "pattern": r"blocked|blocker|false|missing|absent|fail[- ]?closed|unproved|not proved|remain[s]? false",
    },
}


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
            surfaces.append(
                ModuleSurface(
                    path=path,
                    rel_path=path.relative_to(repo_root).as_posix(),
                    group=group,
                    text=path.read_text(),
                )
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
            hits.append(
                {
                    "marker": name,
                    "line": text.count("\n", 0, match.start()) + 1,
                }
            )
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


def selected_strings(scan: dict[str, Any], words: Iterable[str]) -> dict[str, str]:
    needles = tuple(word.lower() for word in words)
    return {
        name: value
        for name, value in scan["string_assignments"].items()
        if any(needle in f"{name} {value}".lower() for needle in needles)
    }


def selected_flags(scan: dict[str, Any], words: Iterable[str]) -> dict[str, bool]:
    needles = tuple(word.lower().replace("-", "").replace("_", "").replace(" ", "") for word in words)
    return {
        name: value
        for name, value in scan["bool_assignments"].items()
        if any(needle in name.lower().replace("-", "").replace("_", "") for needle in needles)
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
    needles = tuple(word.lower().replace("_", "").replace("-", "") for word in words)
    for scan in scans:
        for name, value in scan["bool_assignments"].items():
            normalized = name.lower().replace("_", "").replace("-", "")
            if any(needle in normalized for needle in needles):
                rows.append({"path": scan["path"], "group": scan["group"], "name": name, "value": value})
    return rows


def wc1_status_flags(flags: list[dict[str, Any]]) -> list[dict[str, Any]]:
    proof_words = ("proved", "proof", "theorem", "closed", "closure", "extracted", "extraction")
    wc_words = ("wc1", "weak", "compact", "compactness", "subsequence")
    selected: list[dict[str, Any]] = []
    for flag in flags:
        if flag["group"] != "sprint123_wc1":
            continue
        lower = flag["name"].lower()
        normalized = lower.replace("_", "").replace("-", "")
        if any(word in normalized for word in wc_words) and any(word in lower for word in proof_words):
            selected.append(flag)
    return selected


def route_decision(
    scans: list[dict[str, Any]],
    evidence: dict[str, list[dict[str, Any]]],
    all_flags: list[dict[str, Any]],
) -> tuple[str, list[str], list[str], list[dict[str, Any]]]:
    hard_fail_reasons: list[str] = []
    route_reasons: list[str] = []

    groups_present = {scan["group"] for scan in scans}
    for group, _pattern in SURFACE_PATTERNS:
        if group not in groups_present:
            hard_fail_reasons.append(f"missing required surface group: {group}")

    for scan in scans:
        if scan["promotion_true_detected"]:
            hard_fail_reasons.append(f"{scan['path']}: promotion flag set true")
        if scan["empty_data_declarations"]:
            hard_fail_reasons.append(f"{scan['path']}: empty data declaration present")
        if scan["group"] == "sprint123_wc1" and scan["marker_hits"]:
            details = ", ".join(
                f"{hit['marker']}@L{hit['line']}" for hit in scan["marker_hits"][:12]
            )
            hard_fail_reasons.append(f"{scan['path']}: production marker present ({details})")

    if not evidence["cc1_evidence"]:
        route_reasons.append("missing Sprint121 CC1 evidence")
    if not evidence["sprint122_carrier_evidence"]:
        route_reasons.append("missing Sprint122 carrier evidence")
    if not evidence["wc1_extraction_evidence"]:
        route_reasons.append("missing Sprint123 WC1 extraction evidence")

    required_flags = wc1_status_flags(all_flags)
    if not required_flags:
        route_reasons.append("no explicit Sprint123 WC1 theorem/proof/closure/extraction flags extracted")
    elif not all(flag["value"] is True for flag in required_flags):
        false_names = sorted({flag["name"] for flag in required_flags if flag["value"] is not True})
        route_reasons.append("not all Sprint123 WC1 closure flags are true: " + ", ".join(false_names))

    if hard_fail_reasons or route_reasons:
        return FAIL_CLOSED, hard_fail_reasons, route_reasons, required_flags
    return WC1_CLOSED, [], [], required_flags


def build_summary(repo_root: Path) -> dict[str, Any]:
    surfaces = read_surfaces(repo_root)
    scans = [module_scan(surface) for surface in surfaces]
    evidence = {key: extract_category_evidence(scans, key) for key in EVIDENCE_SPECS}
    all_flags = extract_flag_rows(
        scans,
        (
            "wc1",
            "weak",
            "compact",
            "compactness",
            "subsequence",
            "extraction",
            "proved",
            "closed",
            "theorem",
            "clay",
            "promotion",
            "promoted",
            "blocked",
            "false",
        ),
    )
    decision, hard_fail_reasons, route_reasons, required_flags = route_decision(scans, evidence, all_flags)
    summary: dict[str, Any] = {
        "generated_at_utc": datetime.now(timezone.utc).isoformat(),
        "repo_root": repo_root.as_posix(),
        "route_decision": decision,
        "hard_fail_reasons": hard_fail_reasons,
        "route_reasons": route_reasons,
        "fail_reasons": hard_fail_reasons + route_reasons,
        "scanned_surfaces": {
            group: [surface.rel_path for surface in surfaces if surface.group == group]
            for group, _pattern in SURFACE_PATTERNS
        },
        "fail_closed_scan": scans,
        "wc1_status_flags": required_flags,
        "weak_compactness_flags": all_flags,
        "promotion_flags": extract_flag_rows(scans, ("clay", "promotion", "promoted")),
        "status_note": (
            "The audit reads Sprint121 CC1, Sprint122 carrier, and Sprint123 WC1 Agda surfaces. "
            "Missing required surface groups, true promotion flags, empty data declarations, and "
            "production Sprint123 marker hits are hard failures. Extracted false WC1 theorem flags "
            "produce an honest fail-closed report."
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
        "# YM Sprint 123 WC1 Weak Compactness Audit",
        "",
        f"Route decision: `{summary['route_decision']}`",
        "",
        "## Scanned module surfaces",
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

    render_flag_section(lines, "Sprint123 WC1 Status Flags", summary["wc1_status_flags"])
    render_flag_section(lines, "Weak Compactness Related Flags", summary["weak_compactness_flags"])
    render_flag_section(lines, "Promotion Flags", summary["promotion_flags"])

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
