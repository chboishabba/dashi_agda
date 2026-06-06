#!/usr/bin/env python3
"""Generate the Sprint 107 YM uniformity audit from Agda module text."""

from __future__ import annotations

import argparse
import json
import re
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Iterable


DEFAULT_OUT_DIR = Path("outputs/ym_sprint107_uniformity_audit")
SUMMARY_NAME = "ym_sprint107_uniformity_audit_summary.json"
REPORT_NAME = "ym_sprint107_uniformity_audit.md"
SPRINT106_PATTERN = "DASHI/Physics/Closure/YMSprint106*.agda"
SPRINT107_PATTERN = "DASHI/Physics/Closure/YMSprint107*.agda"

PROMOTION_TRUE = "clayYangMillsPromoted = " + "true"
INCOMPLETE_SURFACE_TOKENS = (
    "post" + "ulate",
    "TO" + "DO",
    "stu" + "b",
    "{" + "!",
    "!" + "}",
)
FAIL_CLOSED = "fail-closed"
ROUTE_DATA_ASSEMBLED = "route data assembled"
UNIFORMITY_THEOREM_STILL_OPEN = "uniformity theorem still open"
UNIFORMITY_THEOREM_PROVED = "uniformity theorem proved"
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


def line_evidence(text: str, needle_pattern: str, limit: int = 12) -> list[dict[str, Any]]:
    pattern = re.compile(needle_pattern, re.IGNORECASE)
    evidence: list[dict[str, Any]] = []
    for index, line in enumerate(text.splitlines(), start=1):
        if pattern.search(line):
            evidence.append({"line": index, "text": line.strip()})
    return evidence[:limit]


def module_scan(surface: ModuleSurface) -> dict[str, Any]:
    bools = bool_assignments(surface.text)
    strings = string_assignments(surface.text)
    token_hits = [token for token in INCOMPLETE_SURFACE_TOKENS if token in surface.text]
    return {
        "path": surface.rel_path,
        "sprint": surface.sprint,
        "clay_promotion_flag": bools.get("clayYangMillsPromoted"),
        "clay_promotion_true_detected": PROMOTION_TRUE in surface.text,
        "incomplete_surface_token_hits": token_hits,
        "bool_assignments": bools,
        "string_assignments": strings,
        "uniformity_line_numbers": source_lines(surface.text, r"uniform|continuum|constant|c\b"),
        "constant_line_numbers": source_lines(surface.text, r"\bC\b|c \*|constant|delta|m_k|k_G|SU\(3\)|adjoint"),
        "hamiltonian_spectral_line_numbers": source_lines(
            surface.text, r"Hamiltonian|spectral|spectrum|transfer[- ]matrix|gap\(T"
        ),
        "target_line_numbers": source_lines(surface.text, r"gap\(T\(a\)\).*m_eff\(a\).*a"),
        "theorem_line_numbers": source_lines(surface.text, r"theorem|proved|claimed|promoted"),
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
    scans: list[dict[str, Any]], words: Iterable[str], line_key: str
) -> list[dict[str, Any]]:
    evidence: list[dict[str, Any]] = []
    for scan in scans:
        strings = selected_strings(scan, words)
        flags = selected_flags(scan, words)
        if strings or flags:
            evidence.append(
                {
                    "path": scan["path"],
                    "sprint": scan["sprint"],
                    "strings": strings,
                    "flags": flags,
                    "line_numbers": scan[line_key],
                }
            )
    return evidence


def extract_transfer_target_evidence(scans: list[dict[str, Any]]) -> list[dict[str, Any]]:
    evidence: list[dict[str, Any]] = []
    for scan in scans:
        strings = {
            name: value
            for name, value in scan["string_assignments"].items()
            if TARGET_FORMULA in value or ("gap(T(a))" in value and "m_eff(a)" in value)
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


def required_uniformity_flags(theorem_flags: list[dict[str, Any]]) -> list[dict[str, Any]]:
    required_words = ("uniform", "continuum", "comparison", "transfergap", "transfer", "lowerbound", "theorem")
    required: list[dict[str, Any]] = []
    for flag in theorem_flags:
        lower = flag["name"].lower()
        if any(word in lower for word in required_words):
            required.append(flag)
    return required


def route_decision(
    sprint107_scans: list[dict[str, Any]], theorem_flags: list[dict[str, Any]]
) -> tuple[str, list[str], list[dict[str, Any]]]:
    fail_reasons: list[str] = []
    for scan in sprint107_scans:
        if scan["clay_promotion_true_detected"]:
            fail_reasons.append(f"{scan['path']}: Clay promotion flag set true")
        if scan["incomplete_surface_token_hits"]:
            fail_reasons.append(f"{scan['path']}: incomplete-surface token present")
    if fail_reasons:
        return FAIL_CLOSED, fail_reasons, []

    required_flags = required_uniformity_flags(theorem_flags)
    if not required_flags:
        return UNIFORMITY_THEOREM_STILL_OPEN, [], required_flags
    if all(flag["value"] is True for flag in required_flags):
        return UNIFORMITY_THEOREM_PROVED, [], required_flags
    return UNIFORMITY_THEOREM_STILL_OPEN, [], required_flags


def build_summary(repo_root: Path) -> dict[str, Any]:
    sprint106 = read_surfaces(repo_root, SPRINT106_PATTERN, "Sprint106")
    sprint107 = read_surfaces(repo_root, SPRINT107_PATTERN, "Sprint107")
    scans = [module_scan(surface) for surface in sprint106 + sprint107]
    sprint107_scans = [scan for scan in scans if scan["sprint"] == "Sprint107"]
    theorem_flags = extract_theorem_flags(scans)
    decision, fail_reasons, required_flags = route_decision(sprint107_scans, theorem_flags)
    return {
        "generated_at_utc": datetime.now(timezone.utc).isoformat(),
        "repo_root": repo_root.as_posix(),
        "route_decision": decision,
        "fail_reasons": fail_reasons,
        "scanned_surfaces": {
            "sprint106": [surface.rel_path for surface in sprint106],
            "sprint107": [surface.rel_path for surface in sprint107],
        },
        "sprint107_fail_closed_scan": sprint107_scans,
        "uniformity_evidence": extract_category_evidence(
            scans, ("uniform", "continuum", "finite-vs-continuum", "survives"), "uniformity_line_numbers"
        ),
        "constant_evidence": extract_category_evidence(
            scans, ("constant", "delta", "c =", "c *", "m_k", "k_g", "su(3)", "adjoint"), "constant_line_numbers"
        ),
        "hamiltonian_spectral_bridge_evidence": extract_category_evidence(
            scans, ("hamiltonian", "spectral", "spectrum", "transfer-matrix", "transfer matrix"), "hamiltonian_spectral_line_numbers"
        ),
        "transfer_target_evidence": extract_transfer_target_evidence(scans),
        "theorem_proved_flags": theorem_flags,
        "required_uniformity_theorem_flags": required_flags,
        "clay_promotion_flags": extract_clay_flags(scans),
        "status_note": (
            "The audit reads actual Sprint 106 and Sprint 107 Agda text. "
            "Sprint 107 is the fail-closed promotion surface; the route remains open unless all required proof flags are true."
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
        line_numbers = item.get("line_numbers") or item.get("target_line_numbers") or []
        if line_numbers:
            joined = ", ".join(str(line) for line in line_numbers[:16])
            lines.append(f"- Lines: {joined}")
        lines.append("")


def render_markdown(summary: dict[str, Any]) -> str:
    lines = [
        "# YM Sprint 107 Uniformity Audit",
        "",
        f"Route decision: `{summary['route_decision']}`",
        "",
        "## Scanned module surfaces",
        "",
    ]
    for sprint in ("sprint106", "sprint107"):
        paths = summary["scanned_surfaces"][sprint]
        if paths:
            for path in paths:
                lines.append(f"- {sprint}: `{path}`")
        else:
            lines.append(f"- {sprint}: no matching Agda modules present")

    render_evidence_section(lines, "Uniformity evidence", summary["uniformity_evidence"])
    render_evidence_section(lines, "Constant evidence", summary["constant_evidence"])
    render_evidence_section(
        lines, "Hamiltonian and spectral bridge evidence", summary["hamiltonian_spectral_bridge_evidence"]
    )

    lines.extend(["", "## Transfer target", ""])
    if summary["transfer_target_evidence"]:
        for item in summary["transfer_target_evidence"]:
            lines.append(f"### `{item['path']}`")
            for name, value in item["strings"].items():
                lines.append(f"- `{name}`: `{value}`")
            if item["target_line_numbers"]:
                joined = ", ".join(str(line) for line in item["target_line_numbers"][:16])
                lines.append(f"- Lines: {joined}")
            lines.append("")
    else:
        lines.append(f"- Target `{TARGET_FORMULA}` was not detected.")

    lines.extend(["", "## Required theorem flags", ""])
    if summary["required_uniformity_theorem_flags"]:
        for flag in summary["required_uniformity_theorem_flags"]:
            lines.append(f"- `{flag['name']}` in `{flag['path']}`: `{str(flag['value']).lower()}`")
    else:
        lines.append("- No required uniformity theorem flags were extracted.")

    lines.extend(["", "## Theorem/proved flags", ""])
    if summary["theorem_proved_flags"]:
        for flag in summary["theorem_proved_flags"]:
            lines.append(f"- `{flag['name']}` in `{flag['path']}`: `{str(flag['value']).lower()}`")
    else:
        lines.append("- No theorem/proved flags were extracted.")

    lines.extend(["", "## Clay flags", ""])
    if summary["clay_promotion_flags"]:
        for flag in summary["clay_promotion_flags"]:
            lines.append(f"- `{flag['name']}` in `{flag['path']}`: `{str(flag['value']).lower()}`")
    else:
        lines.append("- No Clay flags were extracted.")

    lines.extend(["", "## Fail-closed scan", ""])
    if summary["fail_reasons"]:
        for reason in summary["fail_reasons"]:
            lines.append(f"- {reason}")
    else:
        lines.append("- No Sprint 107 fail-closed condition was detected.")
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
