#!/usr/bin/env python3
"""Generate the Sprint 108 YM transfer lower-bound audit from Agda text."""

from __future__ import annotations

import argparse
import json
import re
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Iterable


DEFAULT_OUT_DIR = Path("outputs/ym_sprint108_transfer_lower_bound_audit")
SUMMARY_NAME = "ym_sprint108_transfer_lower_bound_audit_summary.json"
REPORT_NAME = "ym_sprint108_transfer_lower_bound_audit.md"
SPRINT107_PATTERN = "DASHI/Physics/Closure/YMSprint107*.agda"
SPRINT108_PATTERN = "DASHI/Physics/Closure/YMSprint108*.agda"

PROMOTION_TRUE = "clayYangMillsPromoted = " + "true"
INCOMPLETE_SURFACE_TOKENS = (
    "post" + "ulate",
    "TO" + "DO",
    "stu" + "b",
    "{" + "!",
    "!" + "}",
)
AGDA_META_PATTERN = re.compile(r"(?m)^\s*[A-Za-z][A-Za-z0-9']*\s*=\s*\?\s*$")
FAIL_CLOSED = "fail-closed"
TRANSFER_LOWER_BOUND_OPEN = "transfer lower-bound theorem still open"
TRANSFER_LOWER_BOUND_PROVED = "transfer lower-bound theorem proved"
TARGET_FORMULA = "gap(T(a)) >= c * m_eff(a) * a"


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


def incomplete_hits(text: str) -> list[str]:
    hits = [token for token in INCOMPLETE_SURFACE_TOKENS if token in text]
    if AGDA_META_PATTERN.search(text):
        hits.append("rhs-meta")
    return hits


def module_scan(surface: ModuleSurface) -> dict[str, Any]:
    bools = bool_assignments(surface.text)
    strings = string_assignments(surface.text)
    return {
        "path": surface.rel_path,
        "sprint": surface.sprint,
        "clay_promotion_flag": bools.get("clayYangMillsPromoted"),
        "clay_promotion_true_detected": PROMOTION_TRUE in surface.text,
        "incomplete_surface_token_hits": incomplete_hits(surface.text),
        "bool_assignments": bools,
        "string_assignments": strings,
        "mosco_no_pollution_line_numbers": source_lines(surface.text, r"Mosco|pollution|spectral[- ]pollution"),
        "logarithmic_generator_line_numbers": source_lines(surface.text, r"log|generator|functional calculus|H\(a\)|-a\^-1"),
        "uniform_lower_bound_line_numbers": source_lines(
            surface.text, r"uniform|lower[- ]bound|gap\(T\(a\)\)|m_eff\(a\)|positive c|c_transfer"
        ),
        "spectral_gap_transport_line_numbers": source_lines(
            surface.text, r"spectral|Hamiltonian|transfer[- ]matrix|gap transport|gap\(H\)|gap\(T"
        ),
        "target_line_numbers": source_lines(surface.text, r"gap\(T\(a\)\).*m_eff\(a\).*a"),
        "theorem_line_numbers": source_lines(surface.text, r"theorem|proved|claimed|promoted|closed"),
        "evidence_lines": {
            "mosco_no_pollution": line_evidence(surface.text, r"Mosco|pollution|spectral[- ]pollution"),
            "logarithmic_generator_calculus": line_evidence(
                surface.text, r"log|generator|functional calculus|H\(a\)|-a\^-1"
            ),
            "uniform_form_lower_bound": line_evidence(
                surface.text, r"uniform|lower[- ]bound|gap\(T\(a\)\)|m_eff\(a\)|positive c|c_transfer"
            ),
            "spectral_gap_transport": line_evidence(
                surface.text, r"spectral|Hamiltonian|transfer[- ]matrix|gap transport|gap\(H\)|gap\(T"
            ),
        },
    }


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
        if any(needle in lower for needle in needles):
            selected[name] = value
    return selected


def extract_category_evidence(
    scans: list[dict[str, Any]], key: str, words: Iterable[str], line_key: str
) -> list[dict[str, Any]]:
    evidence: list[dict[str, Any]] = []
    for scan in scans:
        strings = selected_strings(scan, words)
        flags = selected_flags(scan, words)
        lines = scan["evidence_lines"][key]
        if strings or flags or lines:
            evidence.append(
                {
                    "path": scan["path"],
                    "sprint": scan["sprint"],
                    "strings": strings,
                    "flags": flags,
                    "line_numbers": scan[line_key],
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
                or "routecomplete" in lower
            ):
                flags.append({"path": scan["path"], "sprint": scan["sprint"], "name": name, "value": value})
    return flags


def extract_clay_flags(scans: list[dict[str, Any]]) -> list[dict[str, Any]]:
    flags: list[dict[str, Any]] = []
    for scan in scans:
        for name, value in scan["bool_assignments"].items():
            if "clay" in name.lower() or "promoted" in name.lower():
                flags.append({"path": scan["path"], "sprint": scan["sprint"], "name": name, "value": value})
    return flags


def required_transfer_lower_bound_flags(theorem_flags: list[dict[str, Any]]) -> list[dict[str, Any]]:
    required: list[dict[str, Any]] = []
    words = (
        "transfer",
        "lowerbound",
        "lower",
        "gap",
        "uniform",
        "continuum",
        "mosco",
        "pollution",
        "hamiltonian",
        "spectral",
        "logarithmic",
        "generator",
        "target",
    )
    for flag in theorem_flags:
        lower = flag["name"].lower()
        if any(word in lower for word in words):
            required.append(flag)
    return required


def route_decision(
    sprint108_scans: list[dict[str, Any]], theorem_flags: list[dict[str, Any]]
) -> tuple[str, list[str], list[dict[str, Any]]]:
    fail_reasons: list[str] = []
    for scan in sprint108_scans:
        if scan["clay_promotion_true_detected"]:
            fail_reasons.append(f"{scan['path']}: Clay promotion flag set true")
        if scan["incomplete_surface_token_hits"]:
            fail_reasons.append(f"{scan['path']}: incomplete-surface marker present")
    if fail_reasons:
        return FAIL_CLOSED, fail_reasons, []

    required_flags = required_transfer_lower_bound_flags(theorem_flags)
    if required_flags and all(flag["value"] is True for flag in required_flags):
        return TRANSFER_LOWER_BOUND_PROVED, [], required_flags
    return TRANSFER_LOWER_BOUND_OPEN, [], required_flags


def build_summary(repo_root: Path) -> dict[str, Any]:
    sprint107 = read_surfaces(repo_root, SPRINT107_PATTERN, "Sprint107")
    sprint108 = read_surfaces(repo_root, SPRINT108_PATTERN, "Sprint108")
    scans = [module_scan(surface) for surface in sprint107 + sprint108]
    sprint108_scans = [scan for scan in scans if scan["sprint"] == "Sprint108"]
    theorem_flags = extract_theorem_flags(scans)
    decision, fail_reasons, required_flags = route_decision(sprint108_scans, theorem_flags)
    return {
        "generated_at_utc": datetime.now(timezone.utc).isoformat(),
        "repo_root": repo_root.as_posix(),
        "route_decision": decision,
        "fail_reasons": fail_reasons,
        "scanned_surfaces": {
            "sprint107": [surface.rel_path for surface in sprint107],
            "sprint108": [surface.rel_path for surface in sprint108],
        },
        "sprint108_fail_closed_scan": sprint108_scans,
        "mosco_no_pollution_evidence": extract_category_evidence(
            scans,
            "mosco_no_pollution",
            ("mosco", "pollution", "spectral-pollution", "spectral pollution"),
            "mosco_no_pollution_line_numbers",
        ),
        "logarithmic_generator_calculus_evidence": extract_category_evidence(
            scans,
            "logarithmic_generator_calculus",
            ("log", "generator", "functional calculus", "h(a)", "-a^-1"),
            "logarithmic_generator_line_numbers",
        ),
        "uniform_form_lower_bound_evidence": extract_category_evidence(
            scans,
            "uniform_form_lower_bound",
            ("uniform", "lower", "bound", "gap(t(a))", "m_eff", "positive c", "c_transfer"),
            "uniform_lower_bound_line_numbers",
        ),
        "spectral_gap_transport_evidence": extract_category_evidence(
            scans,
            "spectral_gap_transport",
            ("spectral", "hamiltonian", "transfer-matrix", "transfer matrix", "transport", "gap(h)", "gap(t"),
            "spectral_gap_transport_line_numbers",
        ),
        "transfer_lower_bound_target_evidence": extract_transfer_target_evidence(scans),
        "theorem_proved_flags": theorem_flags,
        "required_transfer_lower_bound_theorem_flags": required_flags,
        "clay_promotion_flags": extract_clay_flags(scans),
        "status_note": (
            "The audit reads actual Sprint 107 and Sprint 108 Agda text. "
            "Sprint 108 is the fail-closed promotion surface. The transfer lower-bound route remains open unless all extracted required proof flags are true."
        ),
    }


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
        "# YM Sprint 108 Transfer Lower-Bound Audit",
        "",
        f"Route decision: `{summary['route_decision']}`",
        "",
        "## Scanned module surfaces",
        "",
    ]
    for sprint in ("sprint107", "sprint108"):
        paths = summary["scanned_surfaces"][sprint]
        if paths:
            for path in paths:
                lines.append(f"- {sprint}: `{path}`")
        else:
            lines.append(f"- {sprint}: no matching Agda modules present")

    render_evidence_section(lines, "Mosco / No-Pollution Evidence", summary["mosco_no_pollution_evidence"])
    render_evidence_section(
        lines,
        "Logarithmic Generator Calculus Evidence",
        summary["logarithmic_generator_calculus_evidence"],
    )
    render_evidence_section(
        lines, "Uniform Form Lower-Bound Evidence", summary["uniform_form_lower_bound_evidence"]
    )
    render_evidence_section(lines, "Spectral Gap Transport Evidence", summary["spectral_gap_transport_evidence"])

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

    lines.extend(["", "## Required Proof Flags", ""])
    if summary["required_transfer_lower_bound_theorem_flags"]:
        for flag in summary["required_transfer_lower_bound_theorem_flags"]:
            lines.append(f"- `{flag['name']}` in `{flag['path']}`: `{str(flag['value']).lower()}`")
    else:
        lines.append("- No required transfer lower-bound proof flags were extracted.")

    lines.extend(["", "## Theorem / Proved Flags", ""])
    if summary["theorem_proved_flags"]:
        for flag in summary["theorem_proved_flags"]:
            lines.append(f"- `{flag['name']}` in `{flag['path']}`: `{str(flag['value']).lower()}`")
    else:
        lines.append("- No theorem/proved flags were extracted.")

    lines.extend(["", "## Clay Flags", ""])
    if summary["clay_promotion_flags"]:
        for flag in summary["clay_promotion_flags"]:
            lines.append(f"- `{flag['name']}` in `{flag['path']}`: `{str(flag['value']).lower()}`")
    else:
        lines.append("- No Clay flags were extracted.")

    lines.extend(["", "## Fail-Closed Scan", ""])
    if summary["fail_reasons"]:
        for reason in summary["fail_reasons"]:
            lines.append(f"- {reason}")
    else:
        lines.append("- No Sprint 108 fail-closed condition was detected.")
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
    if summary["route_decision"] == FAIL_CLOSED:
        for reason in summary["fail_reasons"]:
            print(f"{FAIL_CLOSED}: {reason}")
        raise SystemExit(1)


if __name__ == "__main__":
    main()
