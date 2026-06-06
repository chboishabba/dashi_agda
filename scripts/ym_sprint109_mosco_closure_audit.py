#!/usr/bin/env python3
"""Generate the Sprint 109 YM Mosco closure audit from Agda text."""

from __future__ import annotations

import argparse
import json
import re
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Iterable


DEFAULT_OUT_DIR = Path("outputs/ym_sprint109_mosco_closure_audit")
SUMMARY_NAME = "ym_sprint109_mosco_closure_audit_summary.json"
REPORT_NAME = "ym_sprint109_mosco_closure_audit.md"
SPRINT108_PATTERN = "DASHI/Physics/Closure/YMSprint108*.agda"
SPRINT109_PATTERN = "DASHI/Physics/Closure/YMSprint109*.agda"

PROMOTION_TRUE = "clayYangMillsPromoted = " + "true"
INCOMPLETE_SURFACE_TOKENS = (
    "post" + "ulate",
    "TO" + "DO",
    "stu" + "b",
    "{" + "!",
    "!" + "}",
)
AGDA_META_PATTERN = re.compile(r"(?m)^\s*[A-Za-z][A-Za-z0-9']*\s*=\s*\?\s*$")
INCOMPLETE_WORD_PATTERNS = {
    "post" + "ulate": re.compile(r"\bpost" + "ulate\b"),
    "TO" + "DO": re.compile(r"\bTO" + "DO\b"),
    "stu" + "b": re.compile(r"\bstu" + "b\b", re.IGNORECASE),
}
DATA_HEADER_PATTERN = re.compile(r"^data\s+\S+.*\bwhere\s*$")

FAIL_CLOSED = "fail-closed"
MOSCO_CLOSURE_PROVED = "mosco closure theorem proved"
TARGET_FORMULA = "gap(T(a)) >= c * m_eff(a) * a"

EVIDENCE_SPECS: dict[str, dict[str, Any]] = {
    "lower_semicontinuity_evidence": {
        "title": "Lower Semicontinuity Evidence",
        "line_key": "lower_semicontinuity_line_numbers",
        "words": ("lower", "semicontinuity", "liminf", "quadratic form", "weakly"),
        "pattern": r"lower[- ]semicontinuity|liminf|quadratic[- ]form|weakly",
    },
    "recovery_sequence_evidence": {
        "title": "Recovery Sequence Evidence",
        "line_key": "recovery_sequence_line_numbers",
        "words": ("recovery", "sequence", "approximant", "matching norm", "energy limit"),
        "pattern": r"recovery|sequence|approximant|matching norm|energy limit",
    },
    "no_bottom_spectrum_pollution_evidence": {
        "title": "No-Bottom-Spectrum Pollution Evidence",
        "line_key": "no_bottom_spectrum_pollution_line_numbers",
        "words": ("no bottom", "bottom-spectrum", "pollution", "spurious", "eigenvalue branch"),
        "pattern": r"no[- ]bottom|bottom[- ]spectrum|pollution|spurious|eigenvalue branch",
    },
    "spectral_liminf_assembly_evidence": {
        "title": "Spectral Liminf Assembly Evidence",
        "line_key": "spectral_liminf_assembly_line_numbers",
        "words": ("spectral", "liminf", "assembly", "lower spectral", "continuum lower"),
        "pattern": r"spectral.*liminf|liminf.*spectral|assembly|lower spectral|continuum lower",
    },
    "transfer_lower_bound_critical_assembly_evidence": {
        "title": "Transfer Lower-Bound Critical Assembly Evidence",
        "line_key": "transfer_lower_bound_critical_assembly_line_numbers",
        "words": ("transfer", "lower", "bound", "critical", "assembly", "gap(t(a))", "m_eff"),
        "pattern": r"transfer.*lower.*bound|lower.*bound.*transfer|critical.*assembly|gap\(T\(a\)\)|m_eff",
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
    assignments: dict[str, bool] = {}
    pattern = re.compile(r"^([A-Za-z][A-Za-z0-9']*)\s*=\s*(true|false)\s*$", re.MULTILINE)
    for name, value in pattern.findall(text):
        assignments[name] = value == "true"
    return assignments


def string_assignments(text: str) -> dict[str, str]:
    assignments: dict[str, str] = {}
    pattern = re.compile(
        r"^([A-Za-z][A-Za-z0-9']*)\s*:\s*String\s*\n"
        r"\1\s*=\s*(?:\n\s*)?\"([^\"]*)\"",
        re.MULTILINE,
    )
    for name, value in pattern.findall(text):
        assignments[name] = value
    return assignments


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
    if AGDA_META_PATTERN.search(text):
        hits.append("rhs-meta")
    return hits


def module_scan(surface: ModuleSurface) -> dict[str, Any]:
    bools = bool_assignments(surface.text)
    strings = string_assignments(surface.text)
    scan: dict[str, Any] = {
        "path": surface.rel_path,
        "sprint": surface.sprint,
        "clay_promotion_flag": bools.get("clayYangMillsPromoted"),
        "clay_promotion_true_detected": PROMOTION_TRUE in surface.text,
        "incomplete_surface_token_hits": incomplete_hits(surface.text),
        "empty_data_declarations": empty_data_declarations(surface.text),
        "bool_assignments": bools,
        "string_assignments": strings,
        "target_line_numbers": source_lines(surface.text, r"gap\(T\(a\)\).*m_eff\(a\).*a"),
        "theorem_line_numbers": source_lines(surface.text, r"theorem|proved|claimed|promoted|closed"),
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
        combined = f"{name} {value}".lower()
        if any(needle in combined for needle in needles):
            selected[name] = value
    return selected


def selected_flags(scan: dict[str, Any], words: Iterable[str]) -> dict[str, bool]:
    needles = tuple(word.lower() for word in words)
    selected: dict[str, bool] = {}
    for name, value in scan["bool_assignments"].items():
        lower = name.lower()
        if any(needle.replace("-", "").replace(" ", "") in lower for needle in needles):
            selected[name] = value
    return selected


def extract_category_evidence(
    scans: list[dict[str, Any]], summary_key: str
) -> list[dict[str, Any]]:
    spec = EVIDENCE_SPECS[summary_key]
    evidence: list[dict[str, Any]] = []
    for scan in scans:
        strings = selected_strings(scan, spec["words"])
        flags = selected_flags(scan, spec["words"])
        lines = scan["evidence_lines"][spec["line_key"]]
        if strings or flags or lines:
            evidence.append(
                {
                    "path": scan["path"],
                    "sprint": scan["sprint"],
                    "strings": strings,
                    "flags": flags,
                    "line_numbers": scan[spec["line_key"]],
                    "line_evidence": lines,
                }
            )
    return evidence


def extract_transfer_target_evidence(scans: list[dict[str, Any]]) -> list[dict[str, Any]]:
    evidence: list[dict[str, Any]] = []
    for scan in scans:
        strings = {
            name: value
            for name, value in scan["string_assignments"].items()
            if TARGET_FORMULA in value
            or ("gap(T(a))" in value and "m_eff(a)" in value and " a" in value)
        }
        if strings or scan["target_line_numbers"]:
            evidence.append(
                {
                    "path": scan["path"],
                    "sprint": scan["sprint"],
                    "strings": strings,
                    "target_line_numbers": scan["target_line_numbers"],
                    "target_formula_detected": bool(strings or scan["target_line_numbers"]),
                }
            )
    return evidence


def extract_theorem_flags(scans: list[dict[str, Any]]) -> list[dict[str, Any]]:
    flags: list[dict[str, Any]] = []
    for scan in scans:
        for name, value in scan["bool_assignments"].items():
            lower = name.lower()
            if (
                "proved" in lower
                or "theorem" in lower
                or "claimed" in lower
                or "closed" in lower
                or "promoted" in lower
                or "closure" in lower
            ):
                flags.append({"path": scan["path"], "sprint": scan["sprint"], "name": name, "value": value})
    return flags


def required_mosco_closure_flags(theorem_flags: list[dict[str, Any]]) -> list[dict[str, Any]]:
    required: list[dict[str, Any]] = []
    words = (
        "mosco",
        "lower",
        "semicontinuity",
        "liminf",
        "recovery",
        "pollution",
        "bottom",
        "spectral",
        "transfer",
        "critical",
        "assembly",
        "closure",
        "theorem",
        "target",
    )
    for flag in theorem_flags:
        lower = flag["name"].lower()
        if any(word in lower for word in words):
            required.append(flag)
    return required


def extract_clay_flags(scans: list[dict[str, Any]]) -> list[dict[str, Any]]:
    flags: list[dict[str, Any]] = []
    for scan in scans:
        for name, value in scan["bool_assignments"].items():
            if "clay" in name.lower() or "promoted" in name.lower():
                flags.append({"path": scan["path"], "sprint": scan["sprint"], "name": name, "value": value})
    return flags


def route_decision(
    sprint109_scans: list[dict[str, Any]], theorem_flags: list[dict[str, Any]]
) -> tuple[str, list[str], list[str], list[dict[str, Any]]]:
    hard_fail_reasons: list[str] = []
    route_reasons: list[str] = []
    for scan in sprint109_scans:
        if scan["clay_promotion_true_detected"]:
            hard_fail_reasons.append(f"{scan['path']}: Clay promotion flag set true")
        if scan["incomplete_surface_token_hits"]:
            hard_fail_reasons.append(f"{scan['path']}: incomplete-surface marker present")
        if scan["empty_data_declarations"]:
            hard_fail_reasons.append(f"{scan['path']}: empty data declaration present")

    if not sprint109_scans:
        route_reasons.append("no Sprint109 Agda module surfaces present")

    required_flags = required_mosco_closure_flags(theorem_flags)
    if not required_flags:
        route_reasons.append("no explicit Mosco closure theorem flags extracted")
    elif not all(flag["value"] is True for flag in required_flags):
        false_names = sorted({flag["name"] for flag in required_flags if flag["value"] is not True})
        route_reasons.append(
            "not all required Mosco closure theorem flags are true: " + ", ".join(false_names)
        )

    if hard_fail_reasons or route_reasons:
        return FAIL_CLOSED, hard_fail_reasons, route_reasons, required_flags
    return MOSCO_CLOSURE_PROVED, [], [], required_flags


def build_summary(repo_root: Path) -> dict[str, Any]:
    sprint108 = read_surfaces(repo_root, SPRINT108_PATTERN, "Sprint108")
    sprint109 = read_surfaces(repo_root, SPRINT109_PATTERN, "Sprint109")
    scans = [module_scan(surface) for surface in sprint108 + sprint109]
    sprint109_scans = [scan for scan in scans if scan["sprint"] == "Sprint109"]
    theorem_flags = extract_theorem_flags(scans)
    decision, hard_fail_reasons, route_reasons, required_flags = route_decision(
        sprint109_scans, theorem_flags
    )
    summary: dict[str, Any] = {
        "generated_at_utc": datetime.now(timezone.utc).isoformat(),
        "repo_root": repo_root.as_posix(),
        "route_decision": decision,
        "hard_fail_reasons": hard_fail_reasons,
        "route_reasons": route_reasons,
        "fail_reasons": hard_fail_reasons + route_reasons,
        "scanned_surfaces": {
            "sprint108": [surface.rel_path for surface in sprint108],
            "sprint109": [surface.rel_path for surface in sprint109],
        },
        "sprint109_fail_closed_scan": sprint109_scans,
        "transfer_lower_bound_target_evidence": extract_transfer_target_evidence(scans),
        "theorem_proved_flags": theorem_flags,
        "required_mosco_closure_theorem_flags": required_flags,
        "clay_promotion_flags": extract_clay_flags(scans),
        "status_note": (
            "The audit reads actual Sprint108 and Sprint109 Agda text. Sprint109 is the "
            "fail-closed Mosco closure surface. The route remains fail-closed unless every "
            "extracted required Mosco closure theorem flag is explicitly true."
        ),
    }
    for key in EVIDENCE_SPECS:
        summary[key] = extract_category_evidence(scans, key)
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
        line_numbers = item.get("line_numbers") or []
        if line_numbers:
            joined = ", ".join(str(line) for line in line_numbers[:16])
            lines.append(f"- Lines: {joined}")
        for row in item.get("line_evidence", [])[:6]:
            lines.append(f"- L{row['line']}: `{row['text']}`")
        lines.append("")


def render_markdown(summary: dict[str, Any]) -> str:
    lines = [
        "# YM Sprint 109 Mosco Closure Audit",
        "",
        f"Route decision: `{summary['route_decision']}`",
        "",
        "## Scanned module surfaces",
        "",
    ]
    for sprint in ("sprint108", "sprint109"):
        paths = summary["scanned_surfaces"][sprint]
        if paths:
            for path in paths:
                lines.append(f"- {sprint}: `{path}`")
        else:
            lines.append(f"- {sprint}: no matching Agda modules present")

    for key, spec in EVIDENCE_SPECS.items():
        render_evidence_section(lines, spec["title"], summary[key])

    lines.extend(["", "## Target Lower Bound", ""])
    if summary["transfer_lower_bound_target_evidence"]:
        for item in summary["transfer_lower_bound_target_evidence"]:
            lines.append(f"### `{item['path']}`")
            for name, value in item["strings"].items():
                lines.append(f"- `{name}`: `{value}`")
            if item["target_line_numbers"]:
                joined = ", ".join(str(line) for line in item["target_line_numbers"][:16])
                lines.append(f"- Lines: {joined}")
            lines.append("")
    else:
        lines.append(f"- Target `{TARGET_FORMULA}` was not detected.")

    lines.extend(["", "## Required Mosco Closure Proof Flags", ""])
    if summary["required_mosco_closure_theorem_flags"]:
        for flag in summary["required_mosco_closure_theorem_flags"]:
            lines.append(f"- `{flag['name']}` in `{flag['path']}`: `{str(flag['value']).lower()}`")
    else:
        lines.append("- No required Mosco closure proof flags were extracted.")

    lines.extend(["", "## Clay Flags", ""])
    if summary["clay_promotion_flags"]:
        for flag in summary["clay_promotion_flags"]:
            lines.append(f"- `{flag['name']}` in `{flag['path']}`: `{str(flag['value']).lower()}`")
    else:
        lines.append("- No Clay flags were extracted.")

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
