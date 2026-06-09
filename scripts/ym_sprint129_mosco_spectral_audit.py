#!/usr/bin/env python3
"""Generate the Sprint 129 Mosco/spectral fail-closed audit."""

from __future__ import annotations

import argparse
import json
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable


AUDIT_ID = "ym_sprint129_mosco_spectral_audit"
DEFAULT_OUT_DIR = Path("outputs/ym_sprint129_mosco_spectral_audit")
SUMMARY_NAME = f"{AUDIT_ID}_summary.json"
REPORT_NAME = f"{AUDIT_ID}.md"
FAIL_CLOSED = "fail-closed"
PASS_DECISION = "sprint129 mosco spectral route aggregate closed"
META_CHAR = chr(63)

EXPECTED_MODULES: tuple[str, ...] = (
    "MoscoLiminfStrongResolventClosure",
    "MoscoRecoveryNoPollutionClosure",
    "SpectralGapTransportClosure",
    "MoscoSpectralRouteLedger",
)
SPRINT128_SUMMARY = Path(
    "outputs/ym_sprint128_closure_audit/ym_sprint128_closure_audit_summary.json"
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
CLAY_PROMOTED_TRUE_PATTERN = re.compile(
    r"(?m)^" + re.escape("clayYangMillsPromoted") + r"\s*=\s*" + re.escape("true") + r"\s*$"
)

MARKER_PATTERNS: tuple[tuple[str, re.Pattern[str]], ...] = (
    ("unimplemented-declaration", re.compile(r"\bpost" + r"ulate\b")),
    ("open-work-token", re.compile(r"\bTO" + r"DO\b")),
    ("placeholder-token", re.compile(r"\bst" + r"ub\b", re.IGNORECASE)),
    ("deferred-proof-token", re.compile(r"future" + r"-proof", re.IGNORECASE)),
    ("agda-incomplete-braces", re.compile(re.escape("{" + "!") + r"|" + re.escape("!" + "}"))),
    ("rhs-meta-character", re.compile(r"(?m)^\s*[A-Za-z][A-Za-z0-9']*\s*=\s*" + re.escape(META_CHAR) + r"\s*$")),
)

GATE_DEFINITIONS: dict[str, dict[str, Any]] = {
    "MC1": {
        "tokens": ("mc1", "moscoliminf", "liminf", "lowersemicontinuity", "strongresolvent"),
        "required_flags": (
            "mc1ClosedFormLowerSemicontinuityProvedHere",
            "mc1TheoremProvedHere",
            "moscoLiminfTheoremProvedHere",
            "strongResolventConvergenceProvedHere",
            "symanzikOaArtifactBoundProvedHere",
            "kuwaeShioyaFrameworkAppliedHere",
        ),
    },
    "MC2": {
        "tokens": ("mc2", "moscorecovery", "recovery", "strongresolvent"),
        "required_flags": (
            "mc2MoscoRecoveryLimsupProvedHere",
            "moscoRecoverySequenceConstructedHere",
        ),
    },
    "MC3": {
        "tokens": ("mc3", "uniformform", "lowerbound", "formbound"),
        "required_flags": (
            "mc3UniformFormLowerBoundProvedHere",
            "uniformFormLowerBoundClosedHere",
        ),
    },
    "MC4": {
        "tokens": ("mc4", "nopollution", "pollution", "bottomspectrum", "mosco"),
        "required_flags": (
            "mc4NoBottomSpectrumPollutionProvedHere",
            "noBottomSpectrumPollutionClosedHere",
            "moscoConvergenceClosedHere",
        ),
    },
    "SC2": {
        "tokens": ("sc2", "spectralgaptransport", "transport", "nonvacuumgap", "continuumhamiltonian"),
        "required_flags": (
            "sc2SpectralGapTransportUnderMoscoProvedHere",
            "bottomSpectrumIsolationTransportProvedHere",
            "positiveNonVacuumGapTransportProvedHere",
            "continuumHamiltonianSpectralGapProvedHere",
        ),
    },
    "OS1": {
        "tokens": ("os1", "osterwalder", "schrader", "wightman", "reflection"),
        "required_flags": (
            "osToWightmanRouteProvedHere",
            "dashiNativeWightmanDistributionsClosedHere",
            "osWightmanPoincareCovarianceProvedHere",
            "wightmanConsequencesLocallyProvedInRepo",
            "os1975Theorem1ProvedInRepo",
        ),
    },
    "FIN": {
        "tokens": ("fin", "final", "submission", "readiness", "clay"),
        "required_flags": (
            "finalSubmissionReadyHere",
            "claySubmissionReadyHere",
            "continuumMassGapProvedHere",
        ),
    },
}


@dataclass(frozen=True)
class ModuleSurface:
    path: Path
    rel_path: str
    expected_name: str
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


def find_expected_modules(repo_root: Path) -> tuple[list[ModuleSurface], dict[str, list[str]]]:
    surfaces: list[ModuleSurface] = []
    candidates_by_name: dict[str, list[str]] = {}
    for expected_name in EXPECTED_MODULES:
        patterns = (
            f"DASHI/Physics/Closure/YMSprint129*{expected_name}*.agda",
            f"DASHI/Physics/Closure/*Sprint129*{expected_name}*.agda",
            f"DASHI/Physics/Closure/*{expected_name}*.agda",
        )
        seen: set[Path] = set()
        candidates: list[Path] = []
        for pattern in patterns:
            for path in sorted(repo_root.glob(pattern)):
                if path.is_file() and path not in seen:
                    seen.add(path)
                    candidates.append(path)
        candidates_by_name[expected_name] = [path.relative_to(repo_root).as_posix() for path in candidates]
        for path in candidates:
            surfaces.append(
                ModuleSurface(
                    path=path,
                    rel_path=path.relative_to(repo_root).as_posix(),
                    expected_name=expected_name,
                    text=read_text(path),
                )
            )
    return surfaces, candidates_by_name


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
    normalized_tokens = tuple(normalize(token) for token in tokens)
    rows: list[dict[str, Any]] = []
    for index, line in enumerate(text.splitlines(), start=1):
        normalized_line = normalize(line)
        if any(token and token in normalized_line for token in normalized_tokens):
            rows.append({"line": index, "text": line.strip()})
            if len(rows) >= limit:
                break
    return rows


def scan_module(surface: ModuleSurface) -> dict[str, Any]:
    bools = bool_assignments(surface.text)
    return {
        "path": surface.rel_path,
        "expected_name": surface.expected_name,
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
        "gate_evidence_lines": {
            gate: source_lines(surface.text, spec["tokens"])
            for gate, spec in GATE_DEFINITIONS.items()
        },
    }


def read_sprint128_summary(repo_root: Path) -> dict[str, Any]:
    path = repo_root / SPRINT128_SUMMARY
    if not path.is_file():
        return {"path": SPRINT128_SUMMARY.as_posix(), "present": False}
    try:
        payload = json.loads(read_text(path))
    except json.JSONDecodeError as exc:
        return {"path": SPRINT128_SUMMARY.as_posix(), "present": True, "json_error": str(exc)}
    return {
        "path": SPRINT128_SUMMARY.as_posix(),
        "present": True,
        "audit_id": payload.get("audit_id"),
        "route_decision": payload.get("route_decision"),
        "fail_reason_count": len(payload.get("fail_reasons", [])),
        "hard_fail_reason_count": len(payload.get("hard_fail_reasons", [])),
        "sprint128_required_gates_closed": payload.get("sprint128_required_gates_closed"),
        "route_required_gates_closed": payload.get("route_required_gates_closed"),
        "clay_promotion_assertion": payload.get("clay_promotion_assertion", {}),
        "route_gate_closed": {
            gate: payload.get("gate_status", {}).get(gate, {}).get("closed")
            for gate in ("MC1", "SC2", "OS1", "FIN")
        },
    }


def iter_flag_values(value: Any) -> Iterable[dict[str, Any]]:
    if isinstance(value, dict):
        if isinstance(value.get("name"), str) and isinstance(value.get("value"), bool):
            yield value
        for child in value.values():
            yield from iter_flag_values(child)
    elif isinstance(value, list):
        for child in value:
            yield from iter_flag_values(child)


def flag_rows(scans: list[dict[str, Any]], gate: str) -> list[dict[str, Any]]:
    spec = GATE_DEFINITIONS[gate]
    names = set(spec["required_flags"])
    token_needles = tuple(normalize(token) for token in spec["tokens"])
    rows: list[dict[str, Any]] = []
    for scan in scans:
        for name, value in scan["bool_assignments"].items():
            normalized_name = normalize(name)
            exact_hit = name in names
            token_hit = any(token and token in normalized_name for token in token_needles)
            closure_hit = any(word in normalized_name for word in ("proved", "closed", "ready", "theorem"))
            if exact_hit or (token_hit and closure_hit):
                rows.append(
                    {
                        "path": scan["path"],
                        "expected_name": scan["expected_name"],
                        "name": name,
                        "value": value,
                        "required": exact_hit,
                    }
                )
    return rows


def gate_evidence(scans: list[dict[str, Any]], gate: str) -> list[dict[str, Any]]:
    token_needles = tuple(normalize(token) for token in GATE_DEFINITIONS[gate]["tokens"])
    rows: list[dict[str, Any]] = []
    for scan in scans:
        strings = {
            name: value
            for name, value in scan["string_assignments"].items()
            if any(token and token in normalize(f"{name} {value}") for token in token_needles)
        }
        records = [
            record
            for record in scan["record_declarations"]
            if any(token and token in normalize(record["name"]) for token in token_needles)
        ]
        lines = scan["gate_evidence_lines"][gate]
        flags = flag_rows([scan], gate)
        if strings or records or lines or flags:
            rows.append(
                {
                    "path": scan["path"],
                    "expected_name": scan["expected_name"],
                    "strings": strings,
                    "records": records,
                    "flags": flags,
                    "line_evidence": lines,
                }
            )
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
    return {
        "closed": not missing and not false_required,
        "required_flags": list(required),
        "missing_required_flags": missing,
        "false_required_flags": false_required,
        "extracted_flags": rows,
        "evidence": gate_evidence(scans, gate),
    }


def prior_true_promotion_flags(prior_summary: dict[str, Any]) -> list[dict[str, Any]]:
    flags: list[dict[str, Any]] = []
    for flag in iter_flag_values(prior_summary.get("clay_promotion_assertion", {})):
        if flag.get("name") == "clayYangMillsPromoted" and flag.get("value") is True:
            flags.append(flag)
    return flags


def build_summary(repo_root: Path) -> dict[str, Any]:
    surfaces, candidates_by_name = find_expected_modules(repo_root)
    scans = [scan_module(surface) for surface in surfaces]
    prior_summary = read_sprint128_summary(repo_root)
    gates = {gate: gate_status(scans, gate) for gate in GATE_DEFINITIONS}

    hard_fail_reasons: list[str] = []
    route_reasons: list[str] = []
    missing_expected = [name for name, paths in candidates_by_name.items() if not paths]
    if missing_expected:
        route_reasons.append("missing expected Sprint129 modules: " + ", ".join(missing_expected))
    for name, paths in candidates_by_name.items():
        sprint129_paths = [path for path in paths if "Sprint129" in path]
        if paths and not sprint129_paths:
            route_reasons.append(f"{name} has matching files, but none are Sprint129-named")
    for scan in scans:
        if scan["clay_promotion_true_detected"]:
            hard_fail_reasons.append(f"{scan['path']}: Clay promotion true assignment detected")
        if scan["empty_data_declarations"]:
            details = ", ".join(f"L{row['line']}" for row in scan["empty_data_declarations"][:12])
            hard_fail_reasons.append(f"{scan['path']}: empty data declaration detected ({details})")
        if scan["marker_hits"]:
            details = ", ".join(f"{hit['marker']}@L{hit['line']}" for hit in scan["marker_hits"][:12])
            hard_fail_reasons.append(f"{scan['path']}: incomplete marker detected ({details})")
    if not prior_summary.get("present"):
        route_reasons.append("Sprint128 closure audit summary is missing")
    if prior_summary.get("json_error"):
        hard_fail_reasons.append(f"{prior_summary['path']}: JSON parse failed: {prior_summary['json_error']}")
    for flag in prior_true_promotion_flags(prior_summary):
        hard_fail_reasons.append(f"{prior_summary['path']}: prior Clay promotion true flag detected: {flag}")

    sprint129_gates = ("MC1", "MC2", "MC3", "MC4", "SC2")
    terminal_gates = ("OS1", "FIN")
    for gate in sprint129_gates:
        if not gates[gate]["closed"]:
            route_reasons.append(f"{gate} Sprint129 closure flags are not closed")
    for gate in terminal_gates:
        if not gates[gate]["closed"]:
            route_reasons.append(f"{gate} terminal route gate is not closed")

    route_aggregate = {
        "required_sprint129_gates": list(sprint129_gates),
        "terminal_route_gates": list(terminal_gates),
        "sprint129_required_gates_closed": all(gates[gate]["closed"] for gate in sprint129_gates),
        "terminal_route_gates_closed": all(gates[gate]["closed"] for gate in terminal_gates),
        "closed": all(gates[gate]["closed"] for gate in sprint129_gates + terminal_gates),
        "fail_closed_until_os1_fin_closed": not all(gates[gate]["closed"] for gate in terminal_gates),
    }
    route_decision = FAIL_CLOSED if hard_fail_reasons or route_reasons else PASS_DECISION
    return {
        "audit_id": AUDIT_ID,
        "route_decision": route_decision,
        "route_aggregate": route_aggregate,
        "hard_fail_reasons": hard_fail_reasons,
        "route_reasons": route_reasons,
        "fail_reasons": hard_fail_reasons + route_reasons,
        "expected_modules": list(EXPECTED_MODULES),
        "module_candidates": candidates_by_name,
        "scanned_surfaces": [scan["path"] for scan in scans],
        "sprint128_summary": prior_summary,
        "gate_status": gates,
        "sprint129_required_gates_closed": route_aggregate["sprint129_required_gates_closed"],
        "route_required_gates_closed": route_aggregate["closed"],
        "clay_promotion_assertion": {
            "no_sprint129_clay_promotion_true": not any(scan["clay_promotion_true_detected"] for scan in scans),
            "no_prior_clay_promotion_true": not prior_true_promotion_flags(prior_summary),
            "sprint129_flags": [
                flag
                for scan in scans
                for flag in scan["clay_promotion_flags"]
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
        false_rows = ", ".join(
            f"`{row['name']}=false in {row['path']}`" for row in status["false_required_flags"]
        )
        lines.append(f"- False required flags: {false_rows}")
    if status["extracted_flags"]:
        for row in status["extracted_flags"]:
            marker = "required" if row["required"] else "supporting"
            lines.append(f"- {marker} `{row['name']}` in `{row['path']}`: `{str(row['value']).lower()}`")
    else:
        lines.append("- No matching Sprint129 flags were extracted.")
    for item in status["evidence"][:4]:
        if item["line_evidence"]:
            line_refs = ", ".join(f"L{row['line']}" for row in item["line_evidence"][:8])
            lines.append(f"- Evidence lines in `{item['path']}`: {line_refs}")


def render_markdown(summary: dict[str, Any]) -> str:
    lines = [
        "# YM Sprint 129 Mosco Spectral Audit",
        "",
        f"Route decision: `{summary['route_decision']}`",
        f"Sprint129 required gates closed: `{str(summary['sprint129_required_gates_closed']).lower()}`",
        f"Route aggregate closed: `{str(summary['route_aggregate']['closed']).lower()}`",
        "",
        "## Scope",
        "",
        "- Scans expected Sprint129 Agda modules: "
        + ", ".join(f"`{name}`" for name in summary["expected_modules"]),
        f"- Reads prior summary: `{summary['sprint128_summary']['path']}`",
        "- Requires direct true Sprint129 flags for MC1, MC2, MC3, MC4, and SC2.",
        "- Keeps the route fail-closed unless OS1 and FIN are closed.",
        "- Rejects any direct Clay promotion true assignment and any forbidden open-work marker.",
        "",
        "## Module Discovery",
        "",
    ]
    for name, paths in summary["module_candidates"].items():
        if paths:
            for path in paths:
                lines.append(f"- {name}: `{path}`")
        else:
            lines.append(f"- {name}: no matching Agda module found")
    for gate in GATE_DEFINITIONS:
        render_gate(lines, gate, summary["gate_status"][gate])
    lines.extend(["", "## Clay Promotion Assertion", ""])
    assertion = summary["clay_promotion_assertion"]
    lines.append(f"- Sprint129 true promotion absent: `{str(assertion['no_sprint129_clay_promotion_true']).lower()}`")
    lines.append(f"- Prior true promotion absent: `{str(assertion['no_prior_clay_promotion_true']).lower()}`")
    if assertion["sprint129_flags"]:
        for flag in assertion["sprint129_flags"]:
            lines.append(f"- `{flag['name']}` in `{flag['path']}`: `{str(flag['value']).lower()}`")
    else:
        lines.append("- No Sprint129 clay promotion flag was extracted.")
    lines.extend(["", "## Fail-Closed Reasons", ""])
    if summary["fail_reasons"]:
        for reason in summary["fail_reasons"]:
            lines.append(f"- {reason}")
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
