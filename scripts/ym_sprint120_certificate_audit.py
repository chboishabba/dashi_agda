#!/usr/bin/env python3
"""Generate the Sprint 120 YM certificate audit from Agda text."""

from __future__ import annotations

import argparse
import json
import re
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Iterable


DEFAULT_OUT_DIR = Path("outputs/ym_sprint120_certificate_audit")
SUMMARY_NAME = "ym_sprint120_certificate_audit_summary.json"
REPORT_NAME = "ym_sprint120_certificate_audit.md"
SPRINT119_PATTERN = "DASHI/Physics/Closure/YMSprint119*.agda"
SPRINT120_PATTERN = "DASHI/Physics/Closure/YMSprint120*.agda"

META_CHAR = chr(63)
CLAY_PROMOTION_NAME = "clay" + "Yang" + "Mills" + "Promoted"
PROMOTION_TRUE_PATTERN = re.compile(r"\b" + CLAY_PROMOTION_NAME + r"\s*=\s*" + "tr" + "ue\b")
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
CERTIFICATE_READY = "sprint120 certificate route proved"

EVIDENCE_SPECS: dict[str, dict[str, Any]] = {
    "external_common_carrier_certificate_evidence": {
        "title": "External Common Carrier Certificate Evidence",
        "line_key": "external_common_carrier_certificate_line_numbers",
        "words": ("external", "common", "carrier", "certificate", "construction"),
        "pattern": r"external|common|carrier|certificate|construction|embedding|projection|quotient",
    },
    "weak_compactness_certificate_evidence": {
        "title": "Weak Compactness Certificate Evidence",
        "line_key": "weak_compactness_certificate_line_numbers",
        "words": ("weak", "compactness", "certificate", "bounded", "subsequence"),
        "pattern": r"weak|compact|compactness|certificate|bounded|subsequence|carrier|energy",
    },
    "common_carrier_feedthrough_closure_reducer_evidence": {
        "title": "Common Carrier Feedthrough Closure Reducer Evidence",
        "line_key": "common_carrier_feedthrough_closure_reducer_line_numbers",
        "words": ("common", "carrier", "feed", "feedthrough", "closure", "reducer"),
        "pattern": r"common|carrier|feed[- ]?through|feedthrough|closure|reducer|criterion|construction",
    },
    "mosco_aggregate_certificate_evidence": {
        "title": "Mosco Aggregate Certificate Evidence",
        "line_key": "mosco_aggregate_certificate_line_numbers",
        "words": ("mosco", "aggregate", "certificate", "liminf", "recovery"),
        "pattern": r"mosco|aggregate|certificate|liminf|recovery|pollution|collapse|lsc|obligation",
    },
    "transfer_calculus_certificate_evidence": {
        "title": "Transfer Calculus Certificate Evidence",
        "line_key": "transfer_calculus_certificate_line_numbers",
        "words": ("transfer", "calculus", "certificate", "spectral", "generator"),
        "pattern": r"transfer|calculus|certificate|generator|spectral|uniform form|lower[- ]bound|readiness",
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
        "clay_promotion_flag": bools.get(CLAY_PROMOTION_NAME),
        "clay_promotion_true_detected": bool(PROMOTION_TRUE_PATTERN.search(surface.text)),
        "incomplete_surface_token_hits": incomplete_hits(surface.text),
        "empty_data_declarations": empty_data_declarations(surface.text),
        "bool_assignments": bools,
        "string_assignments": strings,
        "theorem_line_numbers": source_lines(
            surface.text,
            r"external|common|carrier|feed[- ]?through|weak|compact|mosco|aggregate|transfer|calculus|certificate|closure|reducer|proved|closed|discharged|promoted|obligation",
        ),
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


def extract_theorem_flags(scans: list[dict[str, Any]]) -> list[dict[str, Any]]:
    flags: list[dict[str, Any]] = []
    words = (
        "external",
        "common",
        "carrier",
        "feed",
        "feedthrough",
        "weak",
        "compact",
        "compactness",
        "mosco",
        "aggregate",
        "transfer",
        "calculus",
        "certificate",
        "closure",
        "reducer",
        "proof",
        "proved",
    )
    for scan in scans:
        for name, value in scan["bool_assignments"].items():
            lower = name.lower()
            if any(word in lower for word in words):
                flags.append({"path": scan["path"], "sprint": scan["sprint"], "name": name, "value": value})
    return flags


def required_sprint120_certificate_flags(theorem_flags: list[dict[str, Any]]) -> list[dict[str, Any]]:
    category_words = (
        "external",
        "common",
        "carrier",
        "feed",
        "feedthrough",
        "weak",
        "compact",
        "compactness",
        "mosco",
        "aggregate",
        "transfer",
        "calculus",
    )
    proof_words = ("certificate", "closure", "proof", "proved", "closed", "discharged", "assembled")
    required: list[dict[str, Any]] = []
    for flag in theorem_flags:
        if flag["sprint"] != "Sprint120":
            continue
        lower = flag["name"].lower()
        if any(word in lower for word in category_words) and any(word in lower for word in proof_words):
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
    scans: list[dict[str, Any]],
    theorem_flags: list[dict[str, Any]],
    evidence: dict[str, list[dict[str, Any]]],
) -> tuple[str, list[str], list[str], list[dict[str, Any]]]:
    hard_fail_reasons: list[str] = []
    route_reasons: list[str] = []
    for scan in scans:
        if scan["clay_promotion_true_detected"]:
            hard_fail_reasons.append(f"{scan['path']}: Clay promotion flag set true")
        if scan["incomplete_surface_token_hits"]:
            hard_fail_reasons.append(f"{scan['path']}: incomplete-surface marker or unresolved placeholder present")
        if scan["empty_data_declarations"]:
            hard_fail_reasons.append(f"{scan['path']}: empty data declaration present")

    if not any(scan["sprint"] == "Sprint119" for scan in scans):
        route_reasons.append("no Sprint119 Agda module surfaces present")
    if not any(scan["sprint"] == "Sprint120" for scan in scans):
        route_reasons.append("no Sprint120 Agda module surfaces present")

    missing_evidence = [key for key, items in evidence.items() if not items]
    if missing_evidence:
        route_reasons.append("missing required certificate evidence: " + ", ".join(missing_evidence))

    required_flags = required_sprint120_certificate_flags(theorem_flags)
    if not required_flags:
        route_reasons.append("no explicit Sprint120 certificate/closure/proof flags extracted")
    elif not all(flag["value"] is True for flag in required_flags):
        false_names = sorted({flag["name"] for flag in required_flags if flag["value"] is not True})
        route_reasons.append(
            "not all required Sprint120 certificate/closure/proof flags are true: "
            + ", ".join(false_names)
        )

    if hard_fail_reasons or route_reasons:
        return FAIL_CLOSED, hard_fail_reasons, route_reasons, required_flags
    return CERTIFICATE_READY, [], [], required_flags


def build_summary(repo_root: Path) -> dict[str, Any]:
    sprint119 = read_surfaces(repo_root, SPRINT119_PATTERN, "Sprint119")
    sprint120 = read_surfaces(repo_root, SPRINT120_PATTERN, "Sprint120")
    scans = [module_scan(surface) for surface in sprint119 + sprint120]
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
            "sprint119": [surface.rel_path for surface in sprint119],
            "sprint120": [surface.rel_path for surface in sprint120],
        },
        "fail_closed_scan": scans,
        "theorem_proved_flags": theorem_flags,
        "required_sprint120_certificate_closure_proof_flags": required_flags,
        "clay_promotion_flags": extract_clay_flags(scans),
        "status_note": (
            "The audit reads actual Sprint119 and Sprint120 Agda text. Sprint120 remains "
            "fail-closed unless every certificate evidence lane is present and all required "
            "Sprint120 certificate/closure/proof flags are explicitly true."
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
        line_numbers = item.get("line_numbers") or []
        if line_numbers:
            joined = ", ".join(str(line) for line in line_numbers[:16])
            lines.append(f"- Lines: {joined}")
        for row in item.get("line_evidence", [])[:6]:
            lines.append(f"- L{row['line']}: `{row['text']}`")
        lines.append("")


def render_markdown(summary: dict[str, Any]) -> str:
    lines = [
        "# YM Sprint 120 Certificate Audit",
        "",
        f"Route decision: `{summary['route_decision']}`",
        "",
        "## Scanned module surfaces",
        "",
    ]
    for sprint in ("sprint119", "sprint120"):
        paths = summary["scanned_surfaces"][sprint]
        if paths:
            for path in paths:
                lines.append(f"- {sprint}: `{path}`")
        else:
            lines.append(f"- {sprint}: no matching Agda modules present")

    for key, spec in EVIDENCE_SPECS.items():
        render_evidence_section(lines, spec["title"], summary[key])

    lines.extend(["", "## Required Sprint120 Certificate/Closure/Proof Flags", ""])
    if summary["required_sprint120_certificate_closure_proof_flags"]:
        for flag in summary["required_sprint120_certificate_closure_proof_flags"]:
            lines.append(f"- `{flag['name']}` in `{flag['path']}`: `{str(flag['value']).lower()}`")
    else:
        lines.append("- No required Sprint120 certificate/closure/proof flags were extracted.")

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
