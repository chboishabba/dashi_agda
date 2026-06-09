#!/usr/bin/env python3
"""Generate the Sprint 106 YM transfer-gap audit from Agda module text."""

from __future__ import annotations

import argparse
import json
import re
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


DEFAULT_OUT_DIR = Path("outputs/ym_sprint106_transfer_gap_audit")
SUMMARY_NAME = "ym_sprint106_transfer_gap_audit_summary.json"
REPORT_NAME = "ym_sprint106_transfer_gap_audit.md"
SPRINT105_PATTERN = "DASHI/Physics/Closure/YMSprint105*.agda"
SPRINT106_PATTERN = "DASHI/Physics/Closure/YMSprint106*.agda"

PROMOTION_TRUE = "clayYangMillsPromoted = " + "true"
INCOMPLETE_SURFACE_TOKENS = ("post" + "ulate", "TO" + "DO", "stu" + "b", "{!" + "!}")
ROUTE_DATA_ASSEMBLED = "route data assembled"
THEOREM_STILL_OPEN = "theorem still open"
FAIL_CLOSED = "fail-closed"


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


def string_assignment(text: str, name: str) -> str | None:
    pattern = re.compile(
        rf"^{re.escape(name)}\s*:\s*String\s*\n"
        rf"{re.escape(name)}\s*=\s*\n\s*\"([^\"]*)\"",
        re.MULTILINE,
    )
    match = pattern.search(text)
    return match.group(1) if match else None


def string_assignments(text: str) -> dict[str, str]:
    names = re.findall(r"^([A-Za-z][A-Za-z0-9']*)\s*:\s*String\s*$", text, re.MULTILINE)
    return {name: value for name in names if (value := string_assignment(text, name)) is not None}


def source_lines(text: str, needle_pattern: str) -> list[int]:
    pattern = re.compile(needle_pattern)
    return [index for index, line in enumerate(text.splitlines(), start=1) if pattern.search(line)]


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
        "transfer_line_numbers": source_lines(surface.text, r"transfer|gap\(T|Transfer"),
        "effective_mass_line_numbers": source_lines(surface.text, r"effectiveMass|m_eff|m_k|polymerWeight"),
        "theorem_line_numbers": source_lines(surface.text, r"Theorem|theorem|Proved|proved"),
    }


def extract_transfer_gap_targets(scans: list[dict[str, Any]]) -> list[dict[str, Any]]:
    targets: list[dict[str, Any]] = []
    for scan in scans:
        strings = scan["string_assignments"]
        for name, value in strings.items():
            if "gap" in name.lower() and ("transfer" in name.lower() or "gap(T" in value):
                targets.append(
                    {
                        "path": scan["path"],
                        "name": name,
                        "value": value,
                        "line_numbers": scan["transfer_line_numbers"],
                    }
                )
    return targets


def extract_effective_mass_evidence(scans: list[dict[str, Any]]) -> list[dict[str, Any]]:
    evidence: list[dict[str, Any]] = []
    for scan in scans:
        strings = scan["string_assignments"]
        bools = scan["bool_assignments"]
        string_hits = {
            name: value
            for name, value in strings.items()
            if "mass" in name.lower() or "polymer" in name.lower() or "wc3" in name.lower()
        }
        bool_hits = {
            name: value
            for name, value in bools.items()
            if "mass" in name.lower() or "wc3" in name.lower() or "asymptotic" in name.lower()
        }
        if string_hits or bool_hits:
            evidence.append(
                {
                    "path": scan["path"],
                    "strings": string_hits,
                    "flags": bool_hits,
                    "line_numbers": scan["effective_mass_line_numbers"],
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
                or "theoremproved" in lower
                or "routecomplete" in lower
                or "claimed" in lower
            ):
                flags.append({"path": scan["path"], "name": name, "value": value})
    return flags


def extract_clay_flags(scans: list[dict[str, Any]]) -> list[dict[str, Any]]:
    flags: list[dict[str, Any]] = []
    for scan in scans:
        for name, value in scan["bool_assignments"].items():
            if "clay" in name.lower() or "promoted" in name.lower():
                flags.append({"path": scan["path"], "name": name, "value": value})
    return flags


def transfer_matrix_comparison_status(
    scans: list[dict[str, Any]], theorem_flags: list[dict[str, Any]]
) -> dict[str, Any]:
    explicit_matrix_lines = []
    for scan in scans:
        if re.search(r"transfer[- ]matrix|Transfer[- ]Matrix", scan["path"] + "\n" + " ".join(scan["string_assignments"].values())):
            explicit_matrix_lines.append(scan["path"])
    transfer_proved_flags = [
        flag
        for flag in theorem_flags
        if "transfer" in flag["name"].lower() or "gap" in flag["name"].lower()
    ]
    open_flags = [flag for flag in transfer_proved_flags if flag["value"] is False]
    proved_flags = [flag for flag in transfer_proved_flags if flag["value"] is True]
    if open_flags:
        status = THEOREM_STILL_OPEN
    elif proved_flags:
        status = ROUTE_DATA_ASSEMBLED
    else:
        status = THEOREM_STILL_OPEN
    return {
        "status": status,
        "explicit_transfer_matrix_surface_paths": explicit_matrix_lines,
        "transfer_theorem_flags": transfer_proved_flags,
        "note": (
            "No explicit transfer-matrix comparison theorem surface was found; "
            "the Sprint 105 gap(T(a)) transfer target remains the controlling evidence."
        )
        if not explicit_matrix_lines
        else "Explicit transfer-matrix comparison wording was detected in scanned surfaces.",
    }


def route_decision(
    sprint106_scans: list[dict[str, Any]], theorem_flags: list[dict[str, Any]]
) -> tuple[str, list[str]]:
    fail_reasons: list[str] = []
    for scan in sprint106_scans:
        if scan["clay_promotion_true_detected"]:
            fail_reasons.append(f"{scan['path']}: Clay promotion flag set true")
        if scan["incomplete_surface_token_hits"]:
            fail_reasons.append(f"{scan['path']}: reserved incomplete-surface token present")
    if fail_reasons:
        return FAIL_CLOSED, fail_reasons

    transfer_flags = [
        flag
        for flag in theorem_flags
        if "transfer" in flag["name"].lower() or "gap" in flag["name"].lower()
    ]
    if any(flag["value"] is False for flag in transfer_flags):
        return THEOREM_STILL_OPEN, []
    if any(flag["value"] is True for flag in transfer_flags):
        return ROUTE_DATA_ASSEMBLED, []
    return THEOREM_STILL_OPEN, []


def build_summary(repo_root: Path) -> dict[str, Any]:
    sprint105 = read_surfaces(repo_root, SPRINT105_PATTERN, "Sprint105")
    sprint106 = read_surfaces(repo_root, SPRINT106_PATTERN, "Sprint106")
    scans = [module_scan(surface) for surface in sprint105 + sprint106]
    sprint106_scans = [scan for scan in scans if scan["sprint"] == "Sprint106"]
    transfer_gap_targets = extract_transfer_gap_targets(scans)
    effective_mass_evidence = extract_effective_mass_evidence(scans)
    theorem_flags = extract_theorem_flags(scans)
    clay_flags = extract_clay_flags(scans)
    matrix_status = transfer_matrix_comparison_status(scans, theorem_flags)
    decision, fail_reasons = route_decision(sprint106_scans, theorem_flags)
    return {
        "generated_at_utc": datetime.now(timezone.utc).isoformat(),
        "repo_root": repo_root.as_posix(),
        "route_decision": decision,
        "fail_reasons": fail_reasons,
        "scanned_surfaces": {
            "sprint105": [surface.rel_path for surface in sprint105],
            "sprint106": [surface.rel_path for surface in sprint106],
        },
        "sprint106_fail_closed_scan": sprint106_scans,
        "transfer_gap_targets": transfer_gap_targets,
        "effective_mass_evidence": effective_mass_evidence,
        "transfer_matrix_comparison_status": matrix_status,
        "theorem_proved_flags": theorem_flags,
        "clay_promotion_flags": clay_flags,
        "status_note": (
            "The audit reads actual Sprint 105 and Sprint 106 Agda text. "
            "It does not promote the Clay result unless an explicit proved flag is present."
        ),
    }


def render_markdown(summary: dict[str, Any]) -> str:
    lines = [
        "# YM Sprint 106 Transfer-Gap Audit",
        "",
        f"Route decision: `{summary['route_decision']}`",
        "",
        "## Scanned module surfaces",
        "",
    ]
    for sprint in ("sprint105", "sprint106"):
        paths = summary["scanned_surfaces"][sprint]
        if paths:
            for path in paths:
                lines.append(f"- {sprint}: `{path}`")
        else:
            lines.append(f"- {sprint}: no matching Agda modules present")

    lines.extend(["", "## Transfer-gap target", ""])
    if summary["transfer_gap_targets"]:
        for target in summary["transfer_gap_targets"]:
            lines.append(f"- `{target['name']}` in `{target['path']}`: `{target['value']}`")
    else:
        lines.append("- No transfer-gap target string was extracted from the scanned modules.")

    lines.extend(["", "## Effective-mass evidence", ""])
    if summary["effective_mass_evidence"]:
        for item in summary["effective_mass_evidence"]:
            lines.append(f"### `{item['path']}`")
            for name, value in item["strings"].items():
                lines.append(f"- `{name}`: `{value}`")
            for name, value in item["flags"].items():
                lines.append(f"- `{name}`: `{str(value).lower()}`")
            lines.append("")
    else:
        lines.append("- No effective-mass evidence was extracted from the scanned modules.")

    matrix = summary["transfer_matrix_comparison_status"]
    lines.extend(
        [
            "## Transfer-matrix comparison status",
            "",
            f"- Status: `{matrix['status']}`",
            f"- Note: {matrix['note']}",
            "",
            "## Theorem-proved flags",
            "",
        ]
    )
    if summary["theorem_proved_flags"]:
        for flag in summary["theorem_proved_flags"]:
            lines.append(f"- `{flag['name']}` in `{flag['path']}`: `{str(flag['value']).lower()}`")
    else:
        lines.append("- No theorem/proved flags were extracted.")

    lines.extend(["", "## Clay promotion flags", ""])
    if summary["clay_promotion_flags"]:
        for flag in summary["clay_promotion_flags"]:
            lines.append(f"- `{flag['name']}` in `{flag['path']}`: `{str(flag['value']).lower()}`")
    else:
        lines.append("- No Clay promotion flags were extracted.")

    lines.extend(["", "## Fail-closed scan", ""])
    if summary["fail_reasons"]:
        for reason in summary["fail_reasons"]:
            lines.append(f"- {reason}")
    else:
        lines.append("- No Sprint 106 fail-closed condition was detected.")
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
    if summary["route_decision"] == FAIL_CLOSED:
        for reason in summary["fail_reasons"]:
            print(f"{FAIL_CLOSED}: {reason}")
        raise SystemExit(1)


if __name__ == "__main__":
    main()
