#!/usr/bin/env python3
"""Generate Sprint132 red-team rows for Sprint104 blockers vs Sprint128-131 evidence."""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path
from typing import Any, Iterable


AUDIT_ID = "ym_sprint132_red_team_audit"
DEFAULT_OUT_DIR = Path("outputs/ym_sprint132_red_team_audit")
ROWS_NAME = "red_team_rows.json"
SUMMARY_NAME = f"{AUDIT_ID}_summary.json"
REPORT_NAME = f"{AUDIT_ID}.md"

SPRINT104_SUMMARY = Path(
    "outputs/ym_sprint104_clay_dossier_builder/ym_sprint104_clay_dossier_builder_summary.json"
)
SPRINT131_SUMMARY = Path(
    "outputs/ym_sprint131_final_claim_audit/ym_sprint131_final_claim_audit_summary.json"
)
PRIOR_INTERNAL_SUMMARIES: dict[str, Path] = {
    "Sprint128": Path("outputs/ym_sprint128_closure_audit/ym_sprint128_closure_audit_summary.json"),
    "Sprint129": Path("outputs/ym_sprint129_mosco_spectral_audit/ym_sprint129_mosco_spectral_audit_summary.json"),
    "Sprint130": Path("outputs/ym_sprint130_os_fin_audit/ym_sprint130_os_fin_audit_summary.json"),
}

REQUIRED_INTERNAL_GATES: dict[str, tuple[str, ...]] = {
    "Sprint128": ("CC1", "WC1", "SC1", "SC3", "SY1", "GG1"),
    "Sprint129": ("MC1", "MC2", "MC3", "MC4", "SC2"),
    "Sprint130": ("OS1", "FIN"),
}

BLOCKER_GATE_MAP: dict[str, tuple[str, ...]] = {
    "blockedWightmanDistributions": ("OS1",),
    "blockedPoincareCovariance": ("SY1", "OS1"),
    "blockedSpectrumCondition": ("SC2", "OS1"),
    "blockedAllCompactSimpleG": ("GG1",),
    "blockedNonCircularMassGapProof": ("WC1", "SC1", "SC3", "MC1", "SC2"),
}

INCOMPLETE_MARKERS: tuple[tuple[str, re.Pattern[str]], ...] = (
    ("postulate", re.compile(r"(?<![A-Za-z0-9_])post" + r"ulate(?![A-Za-z0-9_])")),
    ("todo", re.compile(r"(?<![A-Za-z0-9_])TO" + r"DO(?![A-Za-z0-9_])")),
    ("stub", re.compile(r"(?<![A-Za-z0-9_])st" + r"ub(?![A-Za-z0-9_])", re.IGNORECASE)),
    ("skeleton", re.compile(r"(?<![A-Za-z0-9_])skele" + r"ton(?![A-Za-z0-9_])", re.IGNORECASE)),
    ("dummy", re.compile(r"(?<![A-Za-z0-9_])dum" + r"my(?![A-Za-z0-9_])", re.IGNORECASE)),
    ("future-proof", re.compile(r"future" + r"[\s-]*proof", re.IGNORECASE)),
    ("hole", re.compile(r"(?<![A-Za-z0-9_])ho" + r"le(?![A-Za-z0-9_])", re.IGNORECASE)),
    ("agda-hole-braces", re.compile(re.escape("{" + "!") + r"|" + re.escape("!" + "}"))),
    ("rhs-meta", re.compile(r"(?m)^\s*[A-Za-z][A-Za-z0-9']*\s*=\s*\?\s*$")),
)
AGDA_CLAY_PROMOTION_TRUE = re.compile(r"(?m)^\s*clayYangMillsPromoted\s*=\s*true\s*$")
AFFIRMATIVE_PROMOTION_KEYS = {
    "clayYangMillsPromoted",
    "promoted",
    "promotes",
    "promotesClay",
    "clayPromoted",
    "clay_yang_mills_promoted",
}


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--out-dir", type=Path, default=DEFAULT_OUT_DIR)
    return parser.parse_args()


def read_json(path: Path) -> tuple[dict[str, Any] | None, str | None]:
    try:
        return json.loads(path.read_text(encoding="utf-8")), None
    except FileNotFoundError:
        return None, "missing"
    except json.JSONDecodeError as exc:
        return None, f"invalid JSON: {exc}"


def iter_values(value: Any) -> Iterable[Any]:
    yield value
    if isinstance(value, dict):
        for child in value.values():
            yield from iter_values(child)
    elif isinstance(value, list):
        for child in value:
            yield from iter_values(child)


def unique_paths(value: Any) -> list[str]:
    paths: set[str] = set()
    for item in iter_values(value):
        if isinstance(item, dict) and isinstance(item.get("path"), str) and item["path"]:
            paths.add(item["path"])
        elif isinstance(item, str) and (item.startswith("DASHI/") or item.startswith("outputs/")):
            paths.add(item)
    return sorted(paths)


def gate_closed(summary: dict[str, Any], gate: str) -> bool:
    status = summary.get("gate_status", {}).get(gate)
    if isinstance(status, dict):
        return status.get("closed") is True
    return False


def gate_evidence(summary: dict[str, Any], gate: str) -> list[str]:
    status = summary.get("gate_status", {}).get(gate, {})
    return unique_paths(status.get("evidence", []) if isinstance(status, dict) else [])


def sprint132_marker_hits(repo_root: Path) -> list[dict[str, Any]]:
    hits: list[dict[str, Any]] = []
    for path in sorted((repo_root / "DASHI" / "Physics" / "Closure").glob("YMSprint132*.agda")):
        text = path.read_text(encoding="utf-8", errors="replace")
        rel = path.relative_to(repo_root).as_posix()
        for name, pattern in INCOMPLETE_MARKERS:
            for match in pattern.finditer(text):
                hits.append({"path": rel, "line": text.count("\n", 0, match.start()) + 1, "marker": name})
    return hits


def promotion_true_hits(repo_root: Path, summaries: dict[str, dict[str, Any]]) -> list[dict[str, Any]]:
    hits: list[dict[str, Any]] = []
    for source, payload in summaries.items():
        for item in iter_values(payload):
            if not isinstance(item, dict):
                continue
            name = item.get("name")
            if name in AFFIRMATIVE_PROMOTION_KEYS and item.get("value") is True:
                hits.append({"source": source, "surface": "summary-json", "name": name})
            for key, value in item.items():
                if key in AFFIRMATIVE_PROMOTION_KEYS and value is True:
                    hits.append({"source": source, "surface": "summary-json", "key": key})
        for rel in unique_paths(payload):
            path = repo_root / rel
            if path.is_file() and path.suffix == ".agda":
                body = path.read_text(encoding="utf-8", errors="replace")
                for match in AGDA_CLAY_PROMOTION_TRUE.finditer(body):
                    hits.append({
                        "source": source,
                        "surface": rel,
                        "line": body.count("\n", 0, match.start()) + 1,
                    })
    return hits


def build_rows(
    blockers: list[dict[str, Any]],
    claim_status: dict[str, Any],
    external_state: dict[str, Any],
) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for blocker in blockers:
        gap_id = str(blocker.get("gap_id", "unknown"))
        gates = BLOCKER_GATE_MAP.get(gap_id, ())
        closure_rows = []
        evidence_paths: list[str] = []
        for gate in gates:
            status = claim_status.get(gate, {})
            evidence = unique_paths(status.get("evidence", []) if isinstance(status, dict) else [])
            evidence_paths.extend(evidence)
            closure_rows.append({
                "gate": gate,
                "state": status.get("state") if isinstance(status, dict) else "missing",
                "source_sprint": status.get("source_sprint") if isinstance(status, dict) else None,
                "evidence_paths": evidence,
            })
        external_present = external_state.get("present") is not False
        red_team_status = "internal_resolved_external_governance_absent" if closure_rows else "unmapped"
        rows.append({
            "row_id": gap_id,
            "sprint104_blocker": blocker,
            "mapped_internal_gates": closure_rows,
            "internal_resolution": {
                "status": "resolved" if bool(closure_rows) and all(row["state"] == "closed" and row["evidence_paths"] for row in closure_rows) else "unresolved",
                "evidence_paths": sorted(set(evidence_paths)),
            },
            "external_governance": {
                "present": external_present,
                "state": "absent" if not external_present else "present",
                "evidence_paths": unique_paths(external_state.get("evidence", [])),
                "boundary": "external Clay/CMI governance is not supplied by repository-local Sprint128-131 evidence",
            },
            "promotion": {"promoted": False, "promotion_true_allowed": False},
            "red_team_status": red_team_status,
        })
    return rows


def internal_required_objection_rows(rows: list[dict[str, Any]]) -> list[dict[str, Any]]:
    internal_rows: list[dict[str, Any]] = []
    for row in rows:
        internal_rows.append({
            "objection_id": row["row_id"],
            "objection_scope": "internal required objection",
            "status": row["internal_resolution"]["status"],
            "evidence_paths": row["internal_resolution"]["evidence_paths"],
            "mapped_gates": [
                {
                    "gate": gate["gate"],
                    "state": gate["state"],
                    "source_sprint": gate["source_sprint"],
                    "evidence_paths": gate["evidence_paths"],
                }
                for gate in row["mapped_internal_gates"]
            ],
        })
    return internal_rows


def render_markdown(summary: dict[str, Any], rows: list[dict[str, Any]]) -> str:
    lines = [
        "# Sprint132 Red-Team Audit",
        "",
        f"- Route decision: `{summary['route_decision']}`",
        f"- Internal gates state: `{summary['internal_gates_state']}`",
        f"- External governance present: `{str(summary['external_governance_present']).lower()}`",
        f"- Promotion true detected: `{str(summary['promotion_true_detected']).lower()}`",
        "",
        "| Sprint104 blocker | Internal closure | External governance | Evidence paths |",
        "| --- | --- | --- | --- |",
    ]
    for row in rows:
        evidence = "<br>".join(f"`{path}`" for path in row["internal_resolution"]["evidence_paths"])
        gates = ", ".join(f"{gate['gate']}={gate['state']}" for gate in row["mapped_internal_gates"])
        lines.append(
            "| "
            + row["row_id"]
            + " | "
            + gates
            + " | present="
            + str(row["external_governance"]["present"]).lower()
            + " | "
            + evidence
            + " |"
        )
    if summary["fail_reasons"]:
        lines.extend(["", "## Fail Reasons"])
        lines.extend(f"- {reason}" for reason in summary["fail_reasons"])
    return "\n".join(lines) + "\n"


def main() -> int:
    args = parse_args()
    repo_root = args.repo_root.resolve()
    out_dir = args.out_dir if args.out_dir.is_absolute() else repo_root / args.out_dir
    out_dir.mkdir(parents=True, exist_ok=True)

    fail_reasons: list[str] = []
    summaries: dict[str, dict[str, Any]] = {}
    for name, rel in {"Sprint104": SPRINT104_SUMMARY, "Sprint131": SPRINT131_SUMMARY, **PRIOR_INTERNAL_SUMMARIES}.items():
        payload, error = read_json(repo_root / rel)
        if error or payload is None:
            fail_reasons.append(f"{name} summary missing or unreadable at {rel.as_posix()}: {error}")
        else:
            summaries[name] = payload

    blockers = summaries.get("Sprint104", {}).get("blocked_clay_requirements", [])
    if not isinstance(blockers, list) or not blockers:
        fail_reasons.append("Sprint104 blocked_clay_requirements rows are missing")
        blockers = []

    claim_status = summaries.get("Sprint131", {}).get("claim_status", {})
    if not isinstance(claim_status, dict):
        claim_status = {}
        fail_reasons.append("Sprint131 claim_status is missing or malformed")

    missing_internal: list[dict[str, str]] = []
    for sprint, gates in REQUIRED_INTERNAL_GATES.items():
        summary = summaries.get(sprint, {})
        for gate in gates:
            evidence = gate_evidence(summary, gate)
            if not gate_closed(summary, gate) or not evidence:
                missing_internal.append({"sprint": sprint, "gate": gate, "reason": "not closed or missing evidence path"})
    if missing_internal:
        fail_reasons.append("required Sprint128-130 internal gate evidence missing")

    external_state = summaries.get("Sprint131", {}).get("external_acceptance_absent", {})
    if not isinstance(external_state, dict) or external_state.get("present") is not False:
        fail_reasons.append("external governance/acceptance absence is not recorded fail-closed")

    rows = build_rows(blockers, claim_status, external_state if isinstance(external_state, dict) else {})
    internal_objection_rows = internal_required_objection_rows(rows)
    rows_missing_evidence = [row["row_id"] for row in rows if not row["internal_resolution"]["evidence_paths"]]
    if rows_missing_evidence:
        fail_reasons.append("red-team rows lack evidence paths: " + ", ".join(rows_missing_evidence))

    marker_hits = sprint132_marker_hits(repo_root)
    if marker_hits:
        fail_reasons.append("Sprint132 Agda forbidden incomplete markers detected")

    promotion_hits = promotion_true_hits(repo_root, summaries)
    if promotion_hits:
        fail_reasons.append("promotion true appears in audited evidence")

    route_decision = "pass" if not fail_reasons else "fail"
    summary = {
        "audit_id": AUDIT_ID,
        "route_decision": route_decision,
        "source_summaries": {name: rel.as_posix() for name, rel in {"Sprint104": SPRINT104_SUMMARY, "Sprint131": SPRINT131_SUMMARY, **PRIOR_INTERNAL_SUMMARIES}.items()},
        "required_internal_gates": REQUIRED_INTERNAL_GATES,
        "missing_internal_gate_evidence": missing_internal,
        "internal_gates_state": "closed" if not missing_internal else "missing",
        "external_governance": {
            "present": not (isinstance(external_state, dict) and external_state.get("present") is False),
            "state": "absent" if isinstance(external_state, dict) and external_state.get("present") is False else "present",
        },
        "external_governance_present": not (isinstance(external_state, dict) and external_state.get("present") is False),
        "external_governance_state": external_state,
        "rows_lacking_evidence_paths": rows_missing_evidence,
        "sprint132_incomplete_marker_hits": marker_hits,
        "promotion_true_detected": bool(promotion_hits),
        "promotion_true_hits": promotion_hits,
        "internal_required_objection_rows": internal_objection_rows,
        "red_team_rows": rows,
        "fail_reasons": fail_reasons,
    }

    (out_dir / ROWS_NAME).write_text(json.dumps(rows, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    (out_dir / SUMMARY_NAME).write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    (out_dir / REPORT_NAME).write_text(render_markdown(summary, rows), encoding="utf-8")
    return 0 if route_decision == "pass" else 1


if __name__ == "__main__":
    raise SystemExit(main())
