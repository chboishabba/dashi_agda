#!/usr/bin/env python3
"""Generate the Sprint 127 final-readiness fail-closed audit."""

from __future__ import annotations

import argparse
import json
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable


AUDIT_ID = "ym_sprint127_final_readiness_audit"
DEFAULT_OUT_DIR = Path("outputs/ym_sprint127_final_readiness_audit")
SUMMARY_NAME = f"{AUDIT_ID}_summary.json"
REPORT_NAME = f"{AUDIT_ID}.md"
FAIL_CLOSED = "fail-closed"
PASS_DECISION = "submission-readiness gates closed"
META_CHAR = chr(63)

SPRINTS = tuple(range(121, 128))
PRIOR_SUMMARY_GLOBS = tuple(
    f"outputs/ym_sprint{sprint}_*/ym_sprint{sprint}_*_summary.json"
    for sprint in range(121, 127)
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
    ("unsupported-marker", re.compile(r"\bst" + r"ub\b", re.IGNORECASE)),
    ("deferred-proof-token", re.compile(r"future" + r"-proof", re.IGNORECASE)),
    ("agda-incomplete-braces", re.compile(re.escape("{" + "!") + r"|" + re.escape("!" + "}"))),
    ("rhs-question", re.compile(r"(?m)^\s*[A-Za-z][A-Za-z0-9']*\s*=\s*" + re.escape(META_CHAR) + r"\s*$")),
)

GATE_DEFINITIONS: dict[str, dict[str, Any]] = {
    "CC1": {
        "kind": "hard",
        "tokens": ("cc1", "externalcommoncarrier", "commoncarrierconstruction"),
        "required_flags": (
            "cc1ProvedHere",
            "externalCommonCarrierConstructionClosedHere",
            "externalCommonCarrierConstructionTheoremProvedHere",
            "commonCarrierConstructionTheoremProvedHere",
        ),
    },
    "WC1": {
        "kind": "hard",
        "tokens": ("wc1", "weakcompactness", "tightness", "diagonal"),
        "required_flags": (
            "wc1ProvedHere",
            "weakCompactnessClosedHere",
            "weakCompactnessTheoremProvedHere",
            "tightnessTheoremProvedHere",
            "diagonalSubsequenceExtractionTheoremProvedHere",
        ),
    },
    "MC1": {
        "kind": "hard",
        "tokens": ("mc1", "moscoliminf", "closedformlowersemicontinuity"),
        "required_flags": (
            "mc1ClosedFormLowerSemicontinuityProvedHere",
            "mc1TheoremProvedHere",
            "moscoLiminfTheoremProvedHere",
        ),
    },
    "SC1": {
        "kind": "hard",
        "tokens": ("sc1", "loggenerator", "functionalcalculus", "selfadjoint", "domainstability"),
        "required_flags": (
            "sc1SelfAdjointnessProvedHere",
            "sc1LogFunctionalCalculusProvedHere",
            "sc1DomainStabilityProvedHere",
            "sc1ClosedHere",
        ),
    },
    "SC3": {
        "kind": "hard",
        "tokens": ("sc3", "transferlowerbound", "dobrushin", "transfermatrixcomparison"),
        "required_flags": (
            "sc3TransferLowerBoundTheoremProvedHere",
            "dashiNativeTransferTheoremProvedHere",
            "dobrushinPolymerLowerBoundProvedHere",
            "transferMatrixComparisonProvedHere",
            "transferLowerBoundTheoremProvedHere",
        ),
    },
    "SC2": {
        "kind": "terminal",
        "tokens": ("sc2", "spectralgaptransport", "continuumhamiltonian", "nonvacuumgap"),
        "required_flags": (
            "sc2SpectralGapTransportUnderMoscoProvedHere",
            "bottomSpectrumIsolationTransportProvedHere",
            "positiveNonVacuumGapTransportProvedHere",
            "continuumHamiltonianSpectralGapProvedHere",
        ),
    },
    "OS1": {
        "kind": "terminal",
        "tokens": ("os1", "osterwalder", "schrader", "wightman", "reflection"),
        "required_flags": (
            "osToWightmanRouteProvedHere",
            "dashiNativeWightmanDistributionsClosedHere",
            "osWightmanPoincareCovarianceProvedHere",
            "wightmanConsequencesLocallyProvedInRepo",
            "os1975Theorem1ProvedInRepo",
        ),
    },
    "SY1": {
        "kind": "terminal",
        "tokens": ("sy1", "symmetry", "restoration", "poincare", "spectrum", "so4"),
        "required_flags": (
            "anisotropyDecayTheoremProvedHere",
            "so4RestorationTheoremProvedHere",
            "euclideanSchwingerSO4CovarianceProvedHere",
            "spectrumConditionProvedHere",
            "dashiNativePoincareCovarianceClosedHere",
            "dashiNativeSpectrumConditionClosedHere",
        ),
    },
    "GG1": {
        "kind": "terminal",
        "tokens": ("gg1", "compact", "simple", "group", "classification"),
        "required_flags": (
            "allCompactSimpleGTheoremProvedHere",
            "analyticYangMillsTheoremProvedHere",
        ),
    },
    "FIN": {
        "kind": "terminal",
        "tokens": ("fin", "final", "submission", "readiness", "clay"),
        "required_flags": (
            "finalSubmissionReadyHere",
            "claySubmissionReadyHere",
            "continuumMassGapProvedHere",
            "clayYangMillsPromoted",
        ),
    },
}


@dataclass(frozen=True)
class AgdaSurface:
    path: Path
    rel_path: str
    sprint: str
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


def read_agda_surfaces(repo_root: Path) -> list[AgdaSurface]:
    surfaces: list[AgdaSurface] = []
    for sprint in SPRINTS:
        for path in sorted(repo_root.glob(f"DASHI/Physics/Closure/YMSprint{sprint}*.agda")):
            if path.is_file():
                surfaces.append(
                    AgdaSurface(
                        path=path,
                        rel_path=path.relative_to(repo_root).as_posix(),
                        sprint=f"Sprint{sprint}",
                        text=read_text(path),
                    )
                )
    return surfaces


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


def scan_agda_surface(surface: AgdaSurface) -> dict[str, Any]:
    bools = bool_assignments(surface.text)
    strings = string_assignments(surface.text)
    scan: dict[str, Any] = {
        "path": surface.rel_path,
        "sprint": surface.sprint,
        "bool_assignments": bools,
        "bool_references": bool_references(surface.text),
        "string_assignments": strings,
        "record_declarations": record_declarations(surface.text),
        "empty_data_declarations": empty_data_declarations(surface.text),
        "marker_hits": marker_hits(surface.text),
        "clay_promotion_true_detected": bool(CLAY_PROMOTED_TRUE_PATTERN.search(surface.text)),
        "clay_promotion_flags": [
            {"name": name, "value": value}
            for name, value in bools.items()
            if name == "clayYangMillsPromoted"
        ],
    }
    scan["gate_evidence_lines"] = {
        gate: source_lines(surface.text, spec["tokens"])
        for gate, spec in GATE_DEFINITIONS.items()
    }
    return scan


def read_prior_summaries(repo_root: Path) -> list[dict[str, Any]]:
    summaries: list[dict[str, Any]] = []
    seen: set[Path] = set()
    for pattern in PRIOR_SUMMARY_GLOBS:
        for path in sorted(repo_root.glob(pattern)):
            if not path.is_file() or path in seen:
                continue
            seen.add(path)
            try:
                payload = json.loads(read_text(path))
            except json.JSONDecodeError as exc:
                payload = {"json_error": str(exc)}
            summaries.append(
                {
                    "path": path.relative_to(repo_root).as_posix(),
                    "present": True,
                    "audit_id": payload.get("audit_id"),
                    "route_decision": payload.get("route_decision"),
                    "fail_reason_count": len(payload.get("fail_reasons", [])),
                    "hard_fail_reason_count": len(payload.get("hard_fail_reasons", [])),
                    "clay_promotion_flags": payload.get("clay_promotion_flags", []),
                    "payload_keys": sorted(payload.keys()),
                    "json_error": payload.get("json_error"),
                }
            )
    return summaries


def iter_flag_dicts(value: Any) -> Iterable[dict[str, Any]]:
    if isinstance(value, dict):
        if isinstance(value.get("name"), str) and isinstance(value.get("value"), bool):
            yield value
        for child in value.values():
            yield from iter_flag_dicts(child)
    elif isinstance(value, list):
        for child in value:
            yield from iter_flag_dicts(child)


def read_prior_summary_payloads(repo_root: Path) -> list[dict[str, Any]]:
    payloads: list[dict[str, Any]] = []
    seen: set[Path] = set()
    for pattern in PRIOR_SUMMARY_GLOBS:
        for path in sorted(repo_root.glob(pattern)):
            if not path.is_file() or path in seen:
                continue
            seen.add(path)
            try:
                payload = json.loads(read_text(path))
            except json.JSONDecodeError:
                continue
            payloads.append({"path": path.relative_to(repo_root).as_posix(), "payload": payload})
    return payloads


def artifact_presence(repo_root: Path) -> dict[str, Any]:
    agda_by_sprint: dict[str, list[str]] = {}
    outputs_by_sprint: dict[str, list[str]] = {}
    summaries_by_sprint: dict[str, list[str]] = {}
    for sprint in SPRINTS:
        key = f"Sprint{sprint}"
        agda_by_sprint[key] = [
            path.relative_to(repo_root).as_posix()
            for path in sorted(repo_root.glob(f"DASHI/Physics/Closure/YMSprint{sprint}*.agda"))
            if path.is_file()
        ]
        outputs_by_sprint[key] = [
            path.relative_to(repo_root).as_posix()
            for path in sorted(repo_root.glob(f"outputs/ym_sprint{sprint}_*"))
            if path.exists()
        ]
        summaries_by_sprint[key] = [
            path.relative_to(repo_root).as_posix()
            for path in sorted(repo_root.glob(f"outputs/ym_sprint{sprint}_*/ym_sprint{sprint}_*_summary.json"))
            if path.is_file()
        ]
    scripts = [
        path.relative_to(repo_root).as_posix()
        for path in sorted(repo_root.glob("scripts/ym_sprint12[1-7]*.py"))
        if path.is_file()
    ]
    return {
        "agda_by_sprint": agda_by_sprint,
        "outputs_by_sprint": outputs_by_sprint,
        "summaries_by_sprint": summaries_by_sprint,
        "scripts": scripts,
        "missing_agda_sprints": [sprint for sprint, paths in agda_by_sprint.items() if not paths],
        "missing_prior_summary_sprints": [
            sprint for sprint, paths in summaries_by_sprint.items() if sprint != "Sprint127" and not paths
        ],
    }


def gate_flag_rows(scans: list[dict[str, Any]], gate: str) -> list[dict[str, Any]]:
    spec = GATE_DEFINITIONS[gate]
    names = set(spec["required_flags"])
    token_needles = tuple(normalize(token) for token in spec["tokens"])
    rows: list[dict[str, Any]] = []
    for scan in scans:
        for name, value in scan["bool_assignments"].items():
            normalized_name = normalize(name)
            exact_hit = name in names
            token_hit = any(token and token in normalized_name for token in token_needles)
            closure_hit = any(word in normalized_name for word in ("proved", "closed", "ready", "promoted"))
            if exact_hit or (token_hit and closure_hit):
                rows.append(
                    {
                        "path": scan["path"],
                        "sprint": scan["sprint"],
                        "name": name,
                        "value": value,
                        "required": exact_hit,
                    }
                )
    return rows


def prior_gate_flag_rows(prior_payloads: list[dict[str, Any]], gate: str) -> list[dict[str, Any]]:
    spec = GATE_DEFINITIONS[gate]
    names = set(spec["required_flags"])
    token_needles = tuple(normalize(token) for token in spec["tokens"])
    rows: list[dict[str, Any]] = []
    for item in prior_payloads:
        for flag in iter_flag_dicts(item["payload"]):
            name = flag["name"]
            normalized_name = normalize(name)
            exact_hit = name in names
            token_hit = any(token and token in normalized_name for token in token_needles)
            closure_hit = any(word in normalized_name for word in ("proved", "closed", "ready", "promoted"))
            if exact_hit or (token_hit and closure_hit):
                rows.append(
                    {
                        "path": flag.get("path", item["path"]),
                        "summary": item["path"],
                        "sprint": flag.get("group", "prior-summary"),
                        "name": name,
                        "value": flag["value"],
                        "required": exact_hit,
                    }
                )
    return rows


def gate_evidence(scans: list[dict[str, Any]], gate: str) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    spec = GATE_DEFINITIONS[gate]
    token_needles = tuple(normalize(token) for token in spec["tokens"])
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
        flags = gate_flag_rows([scan], gate)
        if strings or records or lines or flags:
            rows.append(
                {
                    "path": scan["path"],
                    "sprint": scan["sprint"],
                    "strings": strings,
                    "records": records,
                    "flags": flags,
                    "line_evidence": lines,
                }
            )
    return rows


def gate_status(scans: list[dict[str, Any]], prior_payloads: list[dict[str, Any]], gate: str) -> dict[str, Any]:
    required = tuple(GATE_DEFINITIONS[gate]["required_flags"])
    agda_flag_rows = gate_flag_rows(scans, gate)
    prior_flag_rows = prior_gate_flag_rows(prior_payloads, gate)
    all_flag_rows = agda_flag_rows + prior_flag_rows
    rows_by_name: dict[str, list[dict[str, Any]]] = {name: [] for name in required}
    for row in all_flag_rows:
        if row["name"] in rows_by_name:
            rows_by_name[row["name"]].append(row)
    missing = [name for name, rows in rows_by_name.items() if not rows]
    false_required = [
        row
        for name, rows in rows_by_name.items()
        for row in rows
        if row["value"] is not True
    ]
    closed = not missing and not false_required
    return {
        "kind": GATE_DEFINITIONS[gate]["kind"],
        "closed": closed,
        "required_flags": list(required),
        "missing_required_flags": missing,
        "false_required_flags": false_required,
        "extracted_flags": all_flag_rows,
        "agda_extracted_flags": agda_flag_rows,
        "prior_summary_extracted_flags": prior_flag_rows,
        "evidence": gate_evidence(scans, gate),
    }


def clay_promotion_inventory(scans: list[dict[str, Any]], prior_summaries: list[dict[str, Any]]) -> dict[str, Any]:
    agda_flags: list[dict[str, Any]] = []
    for scan in scans:
        for flag in scan["clay_promotion_flags"]:
            agda_flags.append(
                {
                    "path": scan["path"],
                    "sprint": scan["sprint"],
                    "name": flag["name"],
                    "value": flag["value"],
                }
            )
    prior_flags: list[dict[str, Any]] = []
    for summary in prior_summaries:
        for flag in summary.get("clay_promotion_flags", []):
            if isinstance(flag, dict):
                prior_flags.append({"summary": summary["path"], **flag})
    true_flags = [
        flag for flag in agda_flags + prior_flags
        if flag.get("name") == "clayYangMillsPromoted" and flag.get("value") is True
    ]
    return {
        "agda_flags": agda_flags,
        "prior_summary_flags": prior_flags,
        "true_flags": true_flags,
        "no_clay_promotion_detected": not true_flags,
    }


def build_summary(repo_root: Path) -> dict[str, Any]:
    surfaces = read_agda_surfaces(repo_root)
    scans = [scan_agda_surface(surface) for surface in surfaces]
    prior_summaries = read_prior_summaries(repo_root)
    prior_payloads = read_prior_summary_payloads(repo_root)
    artifacts = artifact_presence(repo_root)
    gate_statuses = {gate: gate_status(scans, prior_payloads, gate) for gate in GATE_DEFINITIONS}
    clay = clay_promotion_inventory(scans, prior_summaries)

    hard_gates_closed = all(
        status["closed"] for gate, status in gate_statuses.items() if status["kind"] == "hard"
    )
    terminal_gates_closed = all(
        status["closed"] for gate, status in gate_statuses.items() if status["kind"] == "terminal"
    )
    marker_failures = [
        {
            "path": scan["path"],
            "markers": scan["marker_hits"],
            "empty_data_declarations": scan["empty_data_declarations"],
        }
        for scan in scans
        if scan["marker_hits"] or scan["empty_data_declarations"]
    ]
    missing_prior_summaries = artifacts["missing_prior_summary_sprints"]
    missing_agda_sprints = artifacts["missing_agda_sprints"]

    blockers: list[dict[str, Any]] = []
    for gate, status in gate_statuses.items():
        if not status["closed"]:
            blockers.append(
                {
                    "gate": gate,
                    "kind": status["kind"],
                    "missing_required_flags": status["missing_required_flags"],
                    "false_required_flags": status["false_required_flags"],
                    "evidence_paths": [item["path"] for item in status["evidence"]],
                }
            )

    fail_reasons: list[str] = []
    if missing_agda_sprints:
        fail_reasons.append("missing Agda sprint surfaces: " + ", ".join(missing_agda_sprints))
    if missing_prior_summaries:
        fail_reasons.append("missing prior audit summaries: " + ", ".join(missing_prior_summaries))
    if marker_failures:
        fail_reasons.append("incomplete or unsupported Agda surface markers detected")
    if not clay["no_clay_promotion_detected"]:
        fail_reasons.append("Clay promotion true flag detected")
    for blocker in blockers:
        missing = ", ".join(blocker["missing_required_flags"]) or "none"
        false_names = ", ".join(sorted({row["name"] for row in blocker["false_required_flags"]})) or "none"
        fail_reasons.append(
            f"{blocker['gate']} {blocker['kind']} gate not closed; missing={missing}; false={false_names}"
        )

    route_decision = (
        PASS_DECISION
        if hard_gates_closed
        and terminal_gates_closed
        and not missing_agda_sprints
        and not missing_prior_summaries
        and not marker_failures
        and clay["no_clay_promotion_detected"]
        else FAIL_CLOSED
    )

    return {
        "audit_id": AUDIT_ID,
        "route_decision": route_decision,
        "hard_gates_closed": hard_gates_closed,
        "terminal_gates_closed": terminal_gates_closed,
        "gate_status": gate_statuses,
        "exact_blockers": blockers,
        "fail_reasons": fail_reasons,
        "artifact_presence": artifacts,
        "prior_audit_summaries": prior_summaries,
        "clay_promotion_inventory": clay,
        "scanned_agda_surfaces": [scan["path"] for scan in scans],
        "scan_count": len(scans),
        "summary_count": len(prior_summaries),
        "marker_failures": marker_failures,
        "readiness_rule": (
            "Route decision is fail-closed unless every hard gate "
            "CC1/WC1/MC1/SC1/SC3 and every terminal gate SC2/OS1/SY1/GG1/FIN "
            "has direct true required flags, Sprint121-126 summaries are present, "
            "Sprint121-127 Agda surfaces are present, and no Clay promotion true flag is found."
        ),
    }


def render_markdown(summary: dict[str, Any]) -> str:
    lines = [
        "# YM Sprint 127 Final Readiness Audit",
        "",
        f"Route decision: `{summary['route_decision']}`",
        f"Hard gates closed: `{str(summary['hard_gates_closed']).lower()}`",
        f"Terminal gates closed: `{str(summary['terminal_gates_closed']).lower()}`",
        f"Agda surfaces scanned: `{summary['scan_count']}`",
        f"Prior summaries scanned: `{summary['summary_count']}`",
        "",
        "## Readiness Rule",
        "",
        f"- {summary['readiness_rule']}",
        "",
        "## Artifact Presence",
        "",
    ]
    artifacts = summary["artifact_presence"]
    for sprint, paths in artifacts["agda_by_sprint"].items():
        lines.append(f"- {sprint} Agda surfaces: `{len(paths)}`")
    for sprint, paths in artifacts["summaries_by_sprint"].items():
        lines.append(f"- {sprint} audit summaries: `{len(paths)}`")
    lines.append(f"- Sprint121-127 scripts: `{len(artifacts['scripts'])}`")

    lines.extend(["", "## Prior Audit Summaries", ""])
    for item in summary["prior_audit_summaries"]:
        lines.append(
            f"- `{item['path']}`: decision=`{item.get('route_decision')}`, "
            f"fail reasons=`{item.get('fail_reason_count')}`"
        )

    lines.extend(["", "## Gate Status", ""])
    for gate, status in summary["gate_status"].items():
        lines.append(f"### {gate} ({status['kind']})")
        lines.append(f"- Closed: `{str(status['closed']).lower()}`")
        if status["missing_required_flags"]:
            lines.append("- Missing required flags: `" + "`, `".join(status["missing_required_flags"]) + "`")
        if status["false_required_flags"]:
            false_bits = [
                f"{row['name']}={str(row['value']).lower()} in {row['path']}"
                for row in status["false_required_flags"]
            ]
            lines.append("- False required flags: `" + "`, `".join(false_bits) + "`")
        if status["extracted_flags"]:
            lines.append("- Extracted flags:")
            for row in status["extracted_flags"][:18]:
                required = "required" if row["required"] else "supporting"
                lines.append(
                    f"  - `{row['name']}` in `{row['path']}`: "
                    f"`{str(row['value']).lower()}` ({required})"
                )
        evidence_paths = [item["path"] for item in status["evidence"]]
        if evidence_paths:
            lines.append("- Evidence paths: `" + "`, `".join(sorted(set(evidence_paths))[:12]) + "`")
        lines.append("")

    lines.extend(["## Exact Blockers", ""])
    if summary["exact_blockers"]:
        for blocker in summary["exact_blockers"]:
            false_names = sorted({row["name"] for row in blocker["false_required_flags"]})
            lines.append(
                f"- `{blocker['gate']}` ({blocker['kind']}): "
                f"missing `{', '.join(blocker['missing_required_flags']) or 'none'}`; "
                f"false `{', '.join(false_names) or 'none'}`"
            )
    else:
        lines.append("- No gate blocker was extracted.")

    clay = summary["clay_promotion_inventory"]
    lines.extend(["", "## Clay Promotion Inventory", ""])
    lines.append(f"- No Clay promotion detected: `{str(clay['no_clay_promotion_detected']).lower()}`")
    lines.append(f"- Agda Clay promotion flags: `{len(clay['agda_flags'])}`")
    lines.append(f"- Prior-summary Clay promotion flags: `{len(clay['prior_summary_flags'])}`")
    if clay["true_flags"]:
        for flag in clay["true_flags"]:
            lines.append(f"- True promotion flag: `{flag}`")

    lines.extend(["", "## Fail-Closed Reasons", ""])
    if summary["fail_reasons"]:
        for reason in summary["fail_reasons"]:
            lines.append(f"- {reason}")
    else:
        lines.append("- No fail-closed reason was extracted.")
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
    print(f"hard_gates_closed={str(summary['hard_gates_closed']).lower()}")
    print(f"terminal_gates_closed={str(summary['terminal_gates_closed']).lower()}")
    print(f"exact_blocker_count={len(summary['exact_blockers'])}")
    for reason in summary["fail_reasons"]:
        print(f"{FAIL_CLOSED}: {reason}")


if __name__ == "__main__":
    main()
