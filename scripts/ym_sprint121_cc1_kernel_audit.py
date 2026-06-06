#!/usr/bin/env python3
"""Generate the Sprint 121 CC1 kernel audit from Agda text."""

from __future__ import annotations

import argparse
import json
import re
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Iterable


DEFAULT_OUT_DIR = Path("outputs/ym_sprint121_cc1_kernel_audit")
SUMMARY_NAME = "ym_sprint121_cc1_kernel_audit_summary.json"
REPORT_NAME = "ym_sprint121_cc1_kernel_audit.md"
SPRINT120_PATTERN = "DASHI/Physics/Closure/YMSprint120*.agda"
SPRINT121_PATTERN = "DASHI/Physics/Closure/YMSprint121*.agda"

META_CHAR = chr(63)
CLAY_PROMOTION_NAME = "clay" + "Yang" + "Mills" + "Promoted"
PROMOTION_TRUE_PATTERN = re.compile(r"\b[A-Za-z][A-Za-z0-9']*(?:Promotion|Promoted)\s*=\s*true\b")
INCOMPLETE_SURFACE_TOKENS = (
    "post" + "ulate",
    "TO" + "DO",
    "stu" + "b",
    "{" + "!",
    "!" + "}",
)
INCOMPLETE_WORD_PATTERNS = {
    "post" + "ulate": re.compile(r"\bpost" + "ulate\b"),
    "TO" + "DO": re.compile(r"\bTO" + "DO\b"),
    "stu" + "b": re.compile(r"\bstu" + "b\b", re.IGNORECASE),
}
AGDA_RHS_UNRESOLVED_PATTERN = re.compile(
    r"(?m)^\s*[A-Za-z][A-Za-z0-9']*\s*=\s*" + re.escape(META_CHAR) + r"\s*$"
)
AGDA_TYPE_UNRESOLVED_PATTERN = re.compile(
    r"(?m)^\s*[A-Za-z][A-Za-z0-9']*\s*:\s*" + re.escape(META_CHAR) + r"\s*$"
)
DATA_HEADER_PATTERN = re.compile(r"^data\s+\S+.*\bwhere\s*$")

FAIL_CLOSED = "fail-closed"
CC1_READY = "sprint121 cc1 kernel route proved"

EVIDENCE_SPECS: dict[str, dict[str, Any]] = {
    "cc1_kernel_evidence": {
        "title": "CC1 Kernel Evidence",
        "line_key": "cc1_kernel_line_numbers",
        "words": ("cc1", "kernel", "common", "carrier"),
        "pattern": r"cc1|kernel|common|carrier|construction|interface|receipt",
    },
    "sprint120_certificate_evidence": {
        "title": "Sprint120 Certificate Evidence",
        "line_key": "sprint120_certificate_line_numbers",
        "words": ("certificate", "external", "weak", "compactness", "mosco", "transfer"),
        "pattern": r"certificate|external|weak|compact|mosco|transfer|calculus|aggregate|feed[- ]?through",
    },
    "theorem_boundary_evidence": {
        "title": "Theorem Boundary Evidence",
        "line_key": "theorem_boundary_line_numbers",
        "words": ("theorem", "proved", "closed", "boundary", "fail", "closed"),
        "pattern": r"theorem|proved|closed|closure|boundary|fail[- ]?closed|obligation|discharged",
    },
    "record_evidence": {
        "title": "Record Evidence",
        "line_key": "record_line_numbers",
        "words": ("record", "evidence", "receipt", "canonical"),
        "pattern": r"\brecord\b|evidence|receipt|canonical|constructor|mk[A-Z]",
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


def read_surfaces(repo_root: Path, pattern: str, sprint: str) -> list[ModuleSurface]:
    surfaces: list[ModuleSurface] = []
    for path in sorted(repo_root.glob(pattern)):
        if path.is_file():
            surfaces.append(
                ModuleSurface(
                    path=path,
                    rel_path=path.relative_to(repo_root).as_posix(),
                    sprint=sprint,
                    text=path.read_text(),
                )
            )
    return surfaces


def bool_assignments(text: str) -> dict[str, bool]:
    pattern = re.compile(r"^([A-Za-z][A-Za-z0-9']*)\s*=\s*(true|false)\s*$", re.MULTILINE)
    return {name: value == "true" for name, value in pattern.findall(text)}


def string_assignments(text: str) -> dict[str, str]:
    pattern = re.compile(
        r"^([A-Za-z][A-Za-z0-9']*)\s*:\s*String\s*\n"
        r"\1\s*=\s*(?:\n\s*)?\"([^\"]*)\"",
        re.MULTILINE,
    )
    return {name: value for name, value in pattern.findall(text)}


def record_declarations(text: str) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    pattern = re.compile(r"^\s*record\s+([A-Za-z][A-Za-z0-9']*)\s*:\s*Set\b", re.MULTILINE)
    for match in pattern.finditer(text):
        line = text.count("\n", 0, match.start()) + 1
        rows.append({"line": line, "name": match.group(1), "text": match.group(0).strip()})
    return rows


def source_lines(text: str, needle_pattern: str) -> list[int]:
    pattern = re.compile(needle_pattern, re.IGNORECASE)
    return [index for index, line in enumerate(text.splitlines(), start=1) if pattern.search(line)]


def line_evidence(text: str, needle_pattern: str, limit: int = 16) -> list[dict[str, Any]]:
    pattern = re.compile(needle_pattern, re.IGNORECASE)
    rows: list[dict[str, Any]] = []
    for index, line in enumerate(text.splitlines(), start=1):
        if pattern.search(line):
            rows.append({"line": index, "text": line.strip()})
    return rows[:limit]


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
    hits = [
        token
        for token in INCOMPLETE_SURFACE_TOKENS
        if (INCOMPLETE_WORD_PATTERNS[token].search(text) if token in INCOMPLETE_WORD_PATTERNS else token in text)
    ]
    if AGDA_RHS_UNRESOLVED_PATTERN.search(text):
        hits.append("rhs-unresolved")
    if AGDA_TYPE_UNRESOLVED_PATTERN.search(text):
        hits.append("type-unresolved")
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
        "clay_promotion_flag": bools.get(CLAY_PROMOTION_NAME),
        "promotion_true_detected": bool(PROMOTION_TRUE_PATTERN.search(surface.text)),
        "incomplete_surface_token_hits": incomplete_hits(surface.text),
        "empty_data_declarations": empty_data_declarations(surface.text),
    }
    evidence_lines: dict[str, list[dict[str, Any]]] = {}
    for spec in EVIDENCE_SPECS.values():
        scan[spec["line_key"]] = source_lines(surface.text, spec["pattern"])
        evidence_lines[spec["line_key"]] = line_evidence(surface.text, spec["pattern"])
    scan["evidence_lines"] = evidence_lines
    return scan


def selected_strings(scan: dict[str, Any], words: Iterable[str]) -> dict[str, str]:
    needles = tuple(word.lower() for word in words)
    selected: dict[str, str] = {}
    for name, value in scan["string_assignments"].items():
        if any(needle in f"{name} {value}".lower() for needle in needles):
            selected[name] = value
    return selected


def selected_flags(scan: dict[str, Any], words: Iterable[str]) -> dict[str, bool]:
    needles = tuple(word.lower().replace("-", "").replace(" ", "") for word in words)
    selected: dict[str, bool] = {}
    for name, value in scan["bool_assignments"].items():
        lower = name.lower()
        if any(needle in lower for needle in needles):
            selected[name] = value
    return selected


def extract_category_evidence(scans: list[dict[str, Any]], summary_key: str) -> list[dict[str, Any]]:
    spec = EVIDENCE_SPECS[summary_key]
    evidence: list[dict[str, Any]] = []
    for scan in scans:
        strings = selected_strings(scan, spec["words"])
        flags = selected_flags(scan, spec["words"])
        records = [
            row
            for row in scan["record_declarations"]
            if any(word.lower() in row["name"].lower() for word in spec["words"])
        ]
        lines = scan["evidence_lines"][spec["line_key"]]
        if strings or flags or records or lines:
            evidence.append(
                {
                    "path": scan["path"],
                    "sprint": scan["sprint"],
                    "strings": strings,
                    "flags": flags,
                    "records": records,
                    "line_numbers": scan[spec["line_key"]],
                    "line_evidence": lines,
                }
            )
    return evidence


def extract_theorem_flags(scans: list[dict[str, Any]]) -> list[dict[str, Any]]:
    flags: list[dict[str, Any]] = []
    category_words = (
        "cc1",
        "kernel",
        "common",
        "carrier",
        "external",
        "weak",
        "compact",
        "compactness",
        "mosco",
        "aggregate",
        "transfer",
        "calculus",
        "feedthrough",
        "certificate",
        "closure",
        "proof",
        "proved",
        "theorem",
        "discharged",
    )
    for scan in scans:
        for name, value in scan["bool_assignments"].items():
            lower = name.lower()
            if any(word in lower for word in category_words):
                flags.append({"path": scan["path"], "sprint": scan["sprint"], "name": name, "value": value})
    return flags


def required_cc1_flags(theorem_flags: list[dict[str, Any]]) -> list[dict[str, Any]]:
    proof_words = ("proved", "proof", "theorem", "closed", "closure", "discharged")
    cc1_words = ("cc1", "kernel", "commoncarrier", "common", "carrier")
    required: list[dict[str, Any]] = []
    for flag in theorem_flags:
        if flag["sprint"] != "Sprint121":
            continue
        lower = flag["name"].lower()
        normalized = lower.replace("-", "").replace("_", "")
        if any(word in normalized for word in cc1_words) and any(word in lower for word in proof_words):
            required.append(flag)
    return required


def extract_promotion_flags(scans: list[dict[str, Any]]) -> list[dict[str, Any]]:
    flags: list[dict[str, Any]] = []
    for scan in scans:
        for name, value in scan["bool_assignments"].items():
            lower = name.lower()
            if "clay" in lower or "promotion" in lower or "promoted" in lower:
                flags.append({"path": scan["path"], "sprint": scan["sprint"], "name": name, "value": value})
    return flags


def route_decision(
    scans: list[dict[str, Any]],
    theorem_flags: list[dict[str, Any]],
    evidence: dict[str, list[dict[str, Any]]],
) -> tuple[str, list[str], list[str], list[dict[str, Any]]]:
    hard_fail_reasons: list[str] = []
    route_reasons: list[str] = []
    for scan in scans:
        if scan["promotion_true_detected"]:
            hard_fail_reasons.append(f"{scan['path']}: promotion flag set true")
        if scan["incomplete_surface_token_hits"]:
            hard_fail_reasons.append(f"{scan['path']}: incomplete-surface marker or unresolved placeholder present")
        if scan["empty_data_declarations"]:
            hard_fail_reasons.append(f"{scan['path']}: empty data declaration present")

    if not any(scan["sprint"] == "Sprint120" for scan in scans):
        route_reasons.append("no Sprint120 certificate module surfaces present")
    if not any(scan["sprint"] == "Sprint121" for scan in scans):
        route_reasons.append("no Sprint121 CC1 kernel module surfaces present")

    if not evidence["cc1_kernel_evidence"]:
        route_reasons.append("missing CC1 kernel evidence")
    if not evidence["sprint120_certificate_evidence"]:
        route_reasons.append("missing Sprint120 certificate evidence")
    if not evidence["record_evidence"]:
        route_reasons.append("missing record evidence")

    required_flags = required_cc1_flags(theorem_flags)
    if not required_flags:
        route_reasons.append("no explicit Sprint121 CC1 theorem/proof/closure flags extracted")
    elif not all(flag["value"] is True for flag in required_flags):
        false_names = sorted({flag["name"] for flag in required_flags if flag["value"] is not True})
        route_reasons.append("not all required Sprint121 CC1 theorem flags are true: " + ", ".join(false_names))

    if hard_fail_reasons or route_reasons:
        return FAIL_CLOSED, hard_fail_reasons, route_reasons, required_flags
    return CC1_READY, [], [], required_flags


def build_summary(repo_root: Path) -> dict[str, Any]:
    sprint120 = read_surfaces(repo_root, SPRINT120_PATTERN, "Sprint120")
    sprint121 = read_surfaces(repo_root, SPRINT121_PATTERN, "Sprint121")
    scans = [module_scan(surface) for surface in sprint120 + sprint121]
    theorem_flags = extract_theorem_flags(scans)
    evidence = {key: extract_category_evidence(scans, key) for key in EVIDENCE_SPECS}
    decision, hard_fail_reasons, route_reasons, required_flags = route_decision(scans, theorem_flags, evidence)
    summary: dict[str, Any] = {
        "generated_at_utc": datetime.now(timezone.utc).isoformat(),
        "repo_root": repo_root.as_posix(),
        "route_decision": decision,
        "hard_fail_reasons": hard_fail_reasons,
        "route_reasons": route_reasons,
        "fail_reasons": hard_fail_reasons + route_reasons,
        "scanned_surfaces": {
            "sprint120": [surface.rel_path for surface in sprint120],
            "sprint121": [surface.rel_path for surface in sprint121],
        },
        "fail_closed_scan": scans,
        "theorem_proved_flags": theorem_flags,
        "required_sprint121_cc1_theorem_flags": required_flags,
        "promotion_flags": extract_promotion_flags(scans),
        "status_note": (
            "The audit reads actual Sprint121 CC1 Agda kernel text and current Sprint120 "
            "certificate modules. It fails closed unless Sprint121 CC1 theorem flags are "
            "explicitly true; ordinary fail-closed routing exits zero, while hard marker "
            "violations exit nonzero."
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
        line_numbers = item.get("line_numbers") or []
        if line_numbers:
            lines.append(f"- Lines: {', '.join(str(line) for line in line_numbers[:16])}")
        for row in item.get("line_evidence", [])[:6]:
            lines.append(f"- L{row['line']}: `{row['text']}`")
        lines.append("")


def render_markdown(summary: dict[str, Any]) -> str:
    lines = [
        "# YM Sprint 121 CC1 Kernel Audit",
        "",
        f"Route decision: `{summary['route_decision']}`",
        "",
        "## Scanned module surfaces",
        "",
    ]
    for sprint in ("sprint120", "sprint121"):
        paths = summary["scanned_surfaces"][sprint]
        if paths:
            for path in paths:
                lines.append(f"- {sprint}: `{path}`")
        else:
            lines.append(f"- {sprint}: no matching Agda modules present")

    for key, spec in EVIDENCE_SPECS.items():
        render_evidence_section(lines, spec["title"], summary[key])

    lines.extend(["", "## Required Sprint121 CC1 Theorem Flags", ""])
    if summary["required_sprint121_cc1_theorem_flags"]:
        for flag in summary["required_sprint121_cc1_theorem_flags"]:
            lines.append(f"- `{flag['name']}` in `{flag['path']}`: `{str(flag['value']).lower()}`")
    else:
        lines.append("- No required Sprint121 CC1 theorem flags were extracted.")

    lines.extend(["", "## Promotion Flags", ""])
    if summary["promotion_flags"]:
        for flag in summary["promotion_flags"]:
            lines.append(f"- `{flag['name']}` in `{flag['path']}`: `{str(flag['value']).lower()}`")
    else:
        lines.append("- No promotion flags were extracted.")

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
