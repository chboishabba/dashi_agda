#!/usr/bin/env python3
"""Generate the Sprint 130 OS/FIN internal-readiness fail-closed audit."""

from __future__ import annotations

import argparse
import json
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable


AUDIT_ID = "ym_sprint130_os_fin_audit"
DEFAULT_OUT_DIR = Path("outputs/ym_sprint130_os_fin_audit")
SUMMARY_NAME = f"{AUDIT_ID}_summary.json"
REPORT_NAME = f"{AUDIT_ID}.md"
FAIL_CLOSED = "fail-closed"
PASS_DECISION = "sprint130 os1 fin internal readiness closed with external acceptance absent"
META_CHAR = chr(63)

PRIOR_SUMMARIES: tuple[Path, ...] = (
    Path("outputs/ym_sprint128_closure_audit/ym_sprint128_closure_audit_summary.json"),
    Path("outputs/ym_sprint129_mosco_spectral_audit/ym_sprint129_mosco_spectral_audit_summary.json"),
)

BOOL_PATTERN = re.compile(r"^([A-Za-z][A-Za-z0-9']*)\s*=\s*(true|false)\s*$", re.MULTILINE)
BOOL_REF_PATTERN = re.compile(
    r"^([A-Za-z][A-Za-z0-9']*)\s*:\s*Bool\s*\n"
    r"\1\s*=\s*(?:\n\s*)?([A-Za-z][A-Za-z0-9'.-]*)\s*$",
    re.MULTILINE,
)
STRING_PATTERN = re.compile(
    r"^([A-Za-z][A-Za-z0-9']*)\s*:\s*String\s*\n"
    r"\1\s*=\s*(?:\n\s*)?\"([^\"]*)\"",
    re.MULTILINE,
)
RECORD_PATTERN = re.compile(r"^\s*record\s+([A-Za-z][A-Za-z0-9']*)\s*:\s*Set\w*\b", re.MULTILINE)
DATA_HEADER_PATTERN = re.compile(r"^\s*data\s+\S+.*\bwhere\s*$")
CLAY_PROMOTED_TRUE_PATTERN = re.compile(r"(?m)^clayYangMillsPromoted\s*=\s*true\s*$")

MARKER_PATTERNS: tuple[tuple[str, re.Pattern[str]], ...] = (
    ("unimplemented-declaration", re.compile(r"\bpost" + r"ulate\b")),
    ("open-work-token", re.compile(r"\bTO" + r"DO\b")),
    ("placeholder-token", re.compile(r"\bst" + r"ub\b", re.IGNORECASE)),
    ("bare-scaffold-token", re.compile(r"\bskele" + r"ton\b", re.IGNORECASE)),
    ("deferred-proof-token", re.compile(r"future" + r"[\s-]*proof", re.IGNORECASE)),
    ("agda-incomplete-braces", re.compile(re.escape("{" + "!") + r"|" + re.escape("!" + "}"))),
    ("rhs-meta-character", re.compile(r"(?m)^\s*[A-Za-z][A-Za-z0-9']*\s*=\s*" + re.escape(META_CHAR) + r"\s*$")),
)

GATE_DEFINITIONS: dict[str, dict[str, Any]] = {
    "OS1": {
        "tokens": ("os1", "osterwalder", "schrader", "wightman", "reflection"),
        "required_flags": (
            "os1WightmanDistributionsClosedHere",
            "osToWightmanRouteClosedHere",
            "wightmanPoincareCovarianceConsumerClosedHere",
            "wightmanSpectrumConditionConsumerClosedHere",
            "sc2SpectrumTransportConsumerClosedHere",
            "os1PoincareSpectrumFeedClosedHere",
            "os1WightmanConsumerPackageClosedHere",
        ),
    },
    "FIN": {
        "tokens": ("fin", "final", "submission", "readiness", "clay", "internal"),
        "required_flags": (
            "internalCandidatePacketReady",
            "internalSubmissionPacketReady",
        ),
    },
}

EXTERNAL_ACCEPTANCE_NAMES: tuple[str, ...] = (
    "externalAcceptancePresent",
    "externalAcceptanceTokenPresent",
    "externalClayAcceptancePresent",
    "externalClayAcceptanceTokenPresent",
    "clayExternalAcceptancePresent",
    "clayExternalAcceptanceTokenPresent",
    "clayInstituteAcceptancePresent",
    "cmiAcceptancePresent",
)


@dataclass(frozen=True)
class ModuleSurface:
    path: Path
    rel_path: str
    text: str


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--out-dir", type=Path, default=DEFAULT_OUT_DIR)
    return parser.parse_args()


def normalize(value: str) -> str:
    return re.sub(r"[^a-z0-9]", "", value.lower())


def line_number(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def read_text(path: Path) -> str:
    return path.read_text(encoding="utf-8")


def find_sprint130_modules(repo_root: Path) -> list[ModuleSurface]:
    paths = sorted((repo_root / "DASHI" / "Physics" / "Closure").glob("YMSprint130*.agda"))
    return [
        ModuleSurface(path=path, rel_path=path.relative_to(repo_root).as_posix(), text=read_text(path))
        for path in paths
        if path.is_file()
    ]


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


def record_declarations(text: str) -> list[dict[str, Any]]:
    return [
        {"line": line_number(text, match.start()), "name": match.group(1)}
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


def source_lines(text: str, tokens: Iterable[str], limit: int = 12) -> list[dict[str, Any]]:
    needles = tuple(normalize(token) for token in tokens)
    rows: list[dict[str, Any]] = []
    for index, line in enumerate(text.splitlines(), start=1):
        normalized_line = normalize(line)
        if any(needle and needle in normalized_line for needle in needles):
            rows.append({"line": index, "text": line.strip()})
            if len(rows) >= limit:
                break
    return rows


def scan_module(surface: ModuleSurface) -> dict[str, Any]:
    bools = bool_assignments(surface.text)
    return {
        "path": surface.rel_path,
        "bool_assignments": bools,
        "bool_references": bool_references(surface.text),
        "string_assignments": string_assignments(surface.text),
        "record_declarations": record_declarations(surface.text),
        "empty_data_declarations": empty_data_declarations(surface.text),
        "marker_hits": marker_hits(surface.text),
        "clay_promotion_true_detected": bool(CLAY_PROMOTED_TRUE_PATTERN.search(surface.text)),
        "clay_promotion_flags": [
            {"path": surface.rel_path, "name": name, "value": value}
            for name, value in bools.items()
            if name == "clayYangMillsPromoted"
        ],
        "external_acceptance_flags": [
            {"path": surface.rel_path, "name": name, "value": value}
            for name, value in bools.items()
            if name in EXTERNAL_ACCEPTANCE_NAMES
        ],
        "gate_evidence_lines": {
            gate: source_lines(surface.text, spec["tokens"])
            for gate, spec in GATE_DEFINITIONS.items()
        },
    }


def read_prior_summary(repo_root: Path, path: Path) -> dict[str, Any]:
    full_path = repo_root / path
    if not full_path.is_file():
        return {"path": path.as_posix(), "present": False}
    try:
        payload = json.loads(read_text(full_path))
    except json.JSONDecodeError as exc:
        return {"path": path.as_posix(), "present": True, "json_error": str(exc)}
    return {
        "path": path.as_posix(),
        "present": True,
        "audit_id": payload.get("audit_id"),
        "route_decision": payload.get("route_decision"),
        "fail_reason_count": len(payload.get("fail_reasons", [])),
        "hard_fail_reason_count": len(payload.get("hard_fail_reasons", [])),
        "gate_status": {
            gate: payload.get("gate_status", {}).get(gate, {}).get("closed")
            for gate in ("CC1", "WC1", "SC1", "SC3", "SY1", "GG1", "MC1", "MC2", "MC3", "MC4", "SC2", "OS1", "FIN")
        },
        "clay_promotion_assertion": payload.get("clay_promotion_assertion", {}),
    }


def iter_values(value: Any) -> Iterable[Any]:
    yield value
    if isinstance(value, dict):
        for child in value.values():
            yield from iter_values(child)
    elif isinstance(value, list):
        for child in value:
            yield from iter_values(child)


def prior_true_promotion_flags(prior_summary: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        item
        for item in iter_values(prior_summary.get("clay_promotion_assertion", {}))
        if isinstance(item, dict)
        and item.get("name") == "clayYangMillsPromoted"
        and item.get("value") is True
    ]


def flag_rows(scans: list[dict[str, Any]], gate: str) -> list[dict[str, Any]]:
    spec = GATE_DEFINITIONS[gate]
    required = set(spec["required_flags"])
    needles = tuple(normalize(token) for token in spec["tokens"])
    rows: list[dict[str, Any]] = []
    for scan in scans:
        for name, value in scan["bool_assignments"].items():
            normalized_name = normalize(name)
            exact_hit = name in required
            token_hit = any(needle and needle in normalized_name for needle in needles)
            closure_hit = any(word in normalized_name for word in ("proved", "closed", "ready", "theorem"))
            if exact_hit or (token_hit and closure_hit):
                rows.append({"path": scan["path"], "name": name, "value": value, "required": exact_hit})
    return rows


def gate_status(scans: list[dict[str, Any]], gate: str) -> dict[str, Any]:
    required = tuple(GATE_DEFINITIONS[gate]["required_flags"])
    rows = flag_rows(scans, gate)
    rows_by_name: dict[str, list[dict[str, Any]]] = {name: [] for name in required}
    for row in rows:
        if row["name"] in rows_by_name:
            rows_by_name[row["name"]].append(row)
    missing = [name for name, matches in rows_by_name.items() if not matches]
    false_required = [
        row
        for matches in rows_by_name.values()
        for row in matches
        if row["value"] is not True
    ]
    evidence = [
        {
            "path": scan["path"],
            "flags": flag_rows([scan], gate),
            "line_evidence": scan["gate_evidence_lines"][gate],
            "records": [
                record
                for record in scan["record_declarations"]
                if any(normalize(token) in normalize(record["name"]) for token in GATE_DEFINITIONS[gate]["tokens"])
            ],
        }
        for scan in scans
        if flag_rows([scan], gate) or scan["gate_evidence_lines"][gate]
    ]
    return {
        "closed": bool(scans) and not missing and not false_required,
        "required_flags": list(required),
        "missing_required_flags": missing,
        "false_required_flags": false_required,
        "extracted_flags": rows,
        "evidence": evidence,
    }


def build_summary(repo_root: Path) -> dict[str, Any]:
    surfaces = find_sprint130_modules(repo_root)
    scans = [scan_module(surface) for surface in surfaces]
    prior_summaries = [read_prior_summary(repo_root, path) for path in PRIOR_SUMMARIES]
    gates = {gate: gate_status(scans, gate) for gate in GATE_DEFINITIONS}

    hard_fail_reasons: list[str] = []
    route_reasons: list[str] = []
    if not scans:
        route_reasons.append("no Sprint130 Agda modules found under DASHI/Physics/Closure/YMSprint130*.agda")
    for summary in prior_summaries:
        if not summary.get("present"):
            route_reasons.append(f"{summary['path']}: prior summary is missing")
        if summary.get("json_error"):
            hard_fail_reasons.append(f"{summary['path']}: JSON parse failed: {summary['json_error']}")
        for flag in prior_true_promotion_flags(summary):
            hard_fail_reasons.append(f"{summary['path']}: prior Clay promotion true flag detected: {flag}")
    for scan in scans:
        if scan["clay_promotion_true_detected"]:
            hard_fail_reasons.append(f"{scan['path']}: Clay promotion true assignment detected")
        if scan["empty_data_declarations"]:
            details = ", ".join(f"L{row['line']}" for row in scan["empty_data_declarations"][:12])
            hard_fail_reasons.append(f"{scan['path']}: empty data declaration detected ({details})")
        if scan["marker_hits"]:
            details = ", ".join(f"{hit['marker']}@L{hit['line']}" for hit in scan["marker_hits"][:12])
            hard_fail_reasons.append(f"{scan['path']}: incomplete marker detected ({details})")

    for gate, status in gates.items():
        if not status["closed"]:
            route_reasons.append(f"{gate} internal readiness flags are not closed")

    external_true = [
        flag
        for scan in scans
        for flag in scan["external_acceptance_flags"]
        if flag["value"] is True
    ]
    if external_true:
        hard_fail_reasons.append(f"external acceptance true flag detected: {external_true}")

    clay_flags = [
        flag
        for scan in scans
        for flag in scan["clay_promotion_flags"]
    ]
    route_aggregate = {
        "required_internal_gates": ["OS1", "FIN"],
        "os1_internal_readiness_closed": gates["OS1"]["closed"],
        "fin_internal_readiness_closed": gates["FIN"]["closed"],
        "internal_readiness_closed": gates["OS1"]["closed"] and gates["FIN"]["closed"],
        "external_acceptance_absent": not external_true,
        "clayYangMillsPromoted": any(flag["value"] is True for flag in clay_flags),
        "clayYangMillsPromoted_false": bool(clay_flags) and all(flag["value"] is False for flag in clay_flags),
    }
    if not route_aggregate["clayYangMillsPromoted_false"]:
        route_reasons.append("clayYangMillsPromoted=false was not explicitly extracted from every Sprint130 surface")

    route_decision = FAIL_CLOSED if hard_fail_reasons or route_reasons else PASS_DECISION
    return {
        "audit_id": AUDIT_ID,
        "route_decision": route_decision,
        "hard_fail_reasons": hard_fail_reasons,
        "route_reasons": route_reasons,
        "fail_reasons": hard_fail_reasons + route_reasons,
        "scanned_surfaces": [scan["path"] for scan in scans],
        "prior_summaries": prior_summaries,
        "gate_status": gates,
        "route_aggregate": route_aggregate,
        "os1_internal_readiness_closed": route_aggregate["os1_internal_readiness_closed"],
        "fin_internal_readiness_closed": route_aggregate["fin_internal_readiness_closed"],
        "external_acceptance_absent": route_aggregate["external_acceptance_absent"],
        "clay_promotion_assertion": {
            "no_sprint130_clay_promotion_true": not any(scan["clay_promotion_true_detected"] for scan in scans),
            "no_prior_clay_promotion_true": not any(prior_true_promotion_flags(summary) for summary in prior_summaries),
            "clayYangMillsPromoted_false": route_aggregate["clayYangMillsPromoted_false"],
            "sprint130_flags": clay_flags,
        },
        "external_acceptance_assertion": {
            "absent": route_aggregate["external_acceptance_absent"],
            "flags": [
                flag
                for scan in scans
                for flag in scan["external_acceptance_flags"]
            ],
        },
        "forbidden_incomplete_marker_assertion": {
            "closed": not any(scan["marker_hits"] or scan["empty_data_declarations"] for scan in scans),
            "hits": [
                {"path": scan["path"], "marker_hits": scan["marker_hits"], "empty_data_declarations": scan["empty_data_declarations"]}
                for scan in scans
                if scan["marker_hits"] or scan["empty_data_declarations"]
            ],
        },
        "fail_closed_scan": scans,
    }


def render_gate(lines: list[str], gate: str, status: dict[str, Any]) -> None:
    lines.extend(["", f"## {gate} Gate", ""])
    lines.append(f"- Closed: `{str(status['closed']).lower()}`")
    if status["missing_required_flags"]:
        lines.append("- Missing required flags: " + ", ".join(f"`{name}`" for name in status["missing_required_flags"]))
    if status["false_required_flags"]:
        lines.append("- False required flags: " + ", ".join(f"`{row['name']}=false in {row['path']}`" for row in status["false_required_flags"]))
    if status["extracted_flags"]:
        for row in status["extracted_flags"]:
            marker = "required" if row["required"] else "supporting"
            lines.append(f"- {marker} `{row['name']}` in `{row['path']}`: `{str(row['value']).lower()}`")
    else:
        lines.append("- No matching Sprint130 flags were extracted.")
    for item in status["evidence"][:4]:
        if item["line_evidence"]:
            refs = ", ".join(f"L{row['line']}" for row in item["line_evidence"][:8])
            lines.append(f"- Evidence lines in `{item['path']}`: {refs}")


def render_markdown(summary: dict[str, Any]) -> str:
    lines = [
        "# YM Sprint 130 OS FIN Audit",
        "",
        f"Route decision: `{summary['route_decision']}`",
        f"OS1 internal readiness closed: `{str(summary['os1_internal_readiness_closed']).lower()}`",
        f"FIN internal readiness closed: `{str(summary['fin_internal_readiness_closed']).lower()}`",
        f"External acceptance absent: `{str(summary['external_acceptance_absent']).lower()}`",
        f"clayYangMillsPromoted false: `{str(summary['clay_promotion_assertion']['clayYangMillsPromoted_false']).lower()}`",
        "",
        "## Scope",
        "",
        "- Scans Sprint130 Agda modules under `DASHI/Physics/Closure/YMSprint130*.agda`.",
        "- Reads Sprint128 and Sprint129 audit summaries.",
        "- Requires direct true Sprint130 OS1 and FIN internal-readiness flags.",
        "- Rejects any direct Clay promotion true assignment, external acceptance true flag, or forbidden open-work marker.",
        "",
        "## Module Discovery",
        "",
    ]
    if summary["scanned_surfaces"]:
        lines.extend(f"- `{path}`" for path in summary["scanned_surfaces"])
    else:
        lines.append("- No Sprint130 Agda modules found.")
    lines.extend(["", "## Prior Summaries", ""])
    for prior in summary["prior_summaries"]:
        lines.append(f"- `{prior['path']}` present: `{str(prior.get('present', False)).lower()}` route: `{prior.get('route_decision')}`")
    for gate in GATE_DEFINITIONS:
        render_gate(lines, gate, summary["gate_status"][gate])
    lines.extend(["", "## External Acceptance", ""])
    flags = summary["external_acceptance_assertion"]["flags"]
    if flags:
        for flag in flags:
            lines.append(f"- `{flag['name']}` in `{flag['path']}`: `{str(flag['value']).lower()}`")
    else:
        lines.append("- No external acceptance flags were extracted; external acceptance is absent.")
    lines.extend(["", "## Clay Promotion Assertion", ""])
    assertion = summary["clay_promotion_assertion"]
    lines.append(f"- Sprint130 true promotion absent: `{str(assertion['no_sprint130_clay_promotion_true']).lower()}`")
    lines.append(f"- Prior true promotion absent: `{str(assertion['no_prior_clay_promotion_true']).lower()}`")
    if assertion["sprint130_flags"]:
        for flag in assertion["sprint130_flags"]:
            lines.append(f"- `{flag['name']}` in `{flag['path']}`: `{str(flag['value']).lower()}`")
    else:
        lines.append("- No Sprint130 clay promotion flag was extracted.")
    lines.extend(["", "## Fail-Closed Reasons", ""])
    if summary["fail_reasons"]:
        lines.extend(f"- {reason}" for reason in summary["fail_reasons"])
    else:
        lines.append("- No fail-closed condition was detected.")
    return "\n".join(lines)


def write_outputs(summary: dict[str, Any], out_dir: Path) -> None:
    out_dir.mkdir(parents=True, exist_ok=True)
    (out_dir / SUMMARY_NAME).write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    (out_dir / REPORT_NAME).write_text(render_markdown(summary) + "\n", encoding="utf-8")


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
