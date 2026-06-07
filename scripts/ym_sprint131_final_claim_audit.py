#!/usr/bin/env python3
"""Aggregate Sprint128-130 internal Yang-Mills claim-state audit."""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path
from typing import Any, Iterable


AUDIT_ID = "ym_sprint131_final_claim_audit"
DEFAULT_OUT_DIR = Path("outputs/ym_sprint131_final_claim_audit")
SUMMARY_NAME = f"{AUDIT_ID}_summary.json"
REPORT_NAME = f"{AUDIT_ID}.md"

PRIOR_SUMMARIES: tuple[tuple[str, Path], ...] = (
    (
        "Sprint128",
        Path("outputs/ym_sprint128_closure_audit/ym_sprint128_closure_audit_summary.json"),
    ),
    (
        "Sprint129",
        Path("outputs/ym_sprint129_mosco_spectral_audit/ym_sprint129_mosco_spectral_audit_summary.json"),
    ),
    (
        "Sprint130",
        Path("outputs/ym_sprint130_os_fin_audit/ym_sprint130_os_fin_audit_summary.json"),
    ),
)

EXPECTED_CLAIM_SOURCES: dict[str, str] = {
    "CC1": "Sprint128",
    "WC1": "Sprint128",
    "MC1": "Sprint129",
    "MC2": "Sprint129",
    "MC3": "Sprint129",
    "MC4": "Sprint129",
    "SC1": "Sprint128",
    "SC2": "Sprint129",
    "SC3": "Sprint128",
    "SY1": "Sprint128",
    "GG1": "Sprint128",
    "OS1": "Sprint130",
    "FIN": "Sprint130",
}

SPRINT130_EXPECTED_PRIOR_TRUE: tuple[str, ...] = (
    "CC1",
    "WC1",
    "MC1",
    "SC1",
    "SC2",
    "SC3",
    "SY1",
    "GG1",
)

FORBIDDEN_MARKER_KEYS = (
    "marker_hits",
    "empty_data_declarations",
)

CLAY_PROMOTED_NAME = "clayYangMillsPromoted"
TRUE_PROMOTION_PATTERN = re.compile(
    rf"(?m)^\s*{re.escape(CLAY_PROMOTED_NAME)}\s*=\s*true\s*$"
)


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


def bool_flag_rows(value: Any, name: str | None = None) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for item in iter_values(value):
        if not isinstance(item, dict):
            continue
        if name is not None and item.get("name") != name:
            continue
        if isinstance(item.get("value"), bool):
            rows.append(item)
    return rows


def remove_false_required_markers(value: Any) -> Any:
    if isinstance(value, dict):
        return {
            key: remove_false_required_markers(child)
            for key, child in value.items()
            if not (key == "required" and child is False)
        }
    if isinstance(value, list):
        return [remove_false_required_markers(child) for child in value]
    return value


def gate_closed(summary: dict[str, Any], gate: str) -> bool | None:
    status = summary.get("gate_status", {}).get(gate)
    if isinstance(status, dict) and isinstance(status.get("closed"), bool):
        return status["closed"]
    return None


def evidence_for_gate(summary: dict[str, Any], gate: str) -> list[dict[str, Any]]:
    status = summary.get("gate_status", {}).get(gate, {})
    evidence = status.get("evidence", []) if isinstance(status, dict) else []
    paths: set[str] = set()
    if isinstance(evidence, list):
        for item in evidence:
            if not isinstance(item, dict):
                continue
            path = item.get("path")
            if isinstance(path, str) and path:
                paths.add(path)
            for nested in iter_values(item):
                if isinstance(nested, dict):
                    nested_path = nested.get("path")
                    if isinstance(nested_path, str) and nested_path:
                        paths.add(nested_path)
    return [{"path": path} for path in sorted(paths)]


def scan_paths(summary: dict[str, Any]) -> list[str]:
    paths: list[str] = []
    for scan in summary.get("fail_closed_scan", []):
        if isinstance(scan, dict) and isinstance(scan.get("path"), str):
            paths.append(scan["path"])
    return sorted(set(paths))


def marker_failures(summary: dict[str, Any]) -> list[dict[str, Any]]:
    failures: list[dict[str, Any]] = []
    for scan in summary.get("fail_closed_scan", []):
        if not isinstance(scan, dict):
            continue
        path = scan.get("path", "<unknown>")
        for key in FORBIDDEN_MARKER_KEYS:
            rows = scan.get(key, [])
            if rows:
                failures.append({"path": path, "kind": key, "rows": rows})
        if scan.get("clay_promotion_true_detected"):
            failures.append({"path": path, "kind": "clay_promotion_true_detected"})
    return failures


def read_prior_summaries(repo_root: Path) -> tuple[dict[str, dict[str, Any]], list[str]]:
    summaries: dict[str, dict[str, Any]] = {}
    fail_reasons: list[str] = []
    for sprint, rel_path in PRIOR_SUMMARIES:
        payload, error = read_json(repo_root / rel_path)
        if error is not None or payload is None:
            fail_reasons.append(f"{sprint} summary {rel_path.as_posix()} is {error}")
            continue
        summaries[sprint] = payload
    return summaries, fail_reasons


def external_acceptance_state(summary130: dict[str, Any] | None) -> dict[str, Any]:
    if summary130 is None:
        return {"present": True, "evidence": [], "reason": "Sprint130 summary missing"}
    assertion = summary130.get("external_acceptance_assertion", {})
    evidence = assertion.get("flags", []) if isinstance(assertion, dict) else []
    absent = (
        summary130.get("external_acceptance_absent") is True
        and isinstance(assertion, dict)
        and assertion.get("absent") is True
        and bool(evidence)
        and all(row.get("value") is False for row in evidence if isinstance(row, dict))
    )
    return {
        "present": not absent,
        "evidence": evidence,
    }


def clay_promotion_state(summaries: dict[str, dict[str, Any]], repo_root: Path) -> dict[str, Any]:
    flag_rows: list[dict[str, Any]] = []
    true_rows: list[dict[str, Any]] = []
    scanned_paths: set[str] = set()
    true_source_hits: list[str] = []

    for sprint, summary in summaries.items():
        rows = bool_flag_rows(summary.get("clay_promotion_assertion", {}), CLAY_PROMOTED_NAME)
        for row in rows:
            enriched = {"sprint": sprint, **row}
            flag_rows.append(enriched)
            if row.get("value") is True:
                true_rows.append(enriched)
        for rel_path in scan_paths(summary):
            if rel_path in scanned_paths:
                continue
            scanned_paths.add(rel_path)
            path = repo_root / rel_path
            if path.is_file() and TRUE_PROMOTION_PATTERN.search(path.read_text(encoding="utf-8")):
                true_source_hits.append(rel_path)

    return {
        "present": not (bool(flag_rows) and not true_rows and not true_source_hits),
        "flags": flag_rows,
        "true_rows": true_rows,
        "true_source_hits": sorted(true_source_hits),
    }


def build_summary(repo_root: Path) -> dict[str, Any]:
    summaries, fail_reasons = read_prior_summaries(repo_root)
    claim_status: dict[str, dict[str, Any]] = {}
    internal_gate_rows: list[dict[str, Any]] = []

    for claim, sprint in EXPECTED_CLAIM_SOURCES.items():
        source = summaries.get(sprint)
        if source is None:
            claim_status[claim] = {
                "state": "not_closed",
                "source_sprint": sprint,
                "evidence": [],
                "reason": f"{sprint} source summary missing",
            }
            fail_reasons.append(f"{claim} lacks {sprint} source summary")
            continue

        closed = gate_closed(source, claim)
        evidence = evidence_for_gate(source, claim)
        internal_gate_rows.append({"gate": claim, "internal_gate_closed": closed is True})
        claim_status[claim] = {
            "state": "closed" if closed is True else "not_closed",
            "source_sprint": sprint,
            "source_path": next(path.as_posix() for label, path in PRIOR_SUMMARIES if label == sprint),
            "evidence": evidence,
        }
        if closed is not True:
            fail_reasons.append(f"{claim} is not closed in {sprint} summary")
        if not evidence:
            fail_reasons.append(f"{claim} has no evidence rows in {sprint} summary")

    for sprint, summary in summaries.items():
        hard_fail_reasons = summary.get("hard_fail_reasons", [])
        if hard_fail_reasons:
            fail_reasons.append(f"{sprint} has hard fail reasons: {hard_fail_reasons}")
        for failure in marker_failures(summary):
            fail_reasons.append(f"{sprint} forbidden marker in {failure.get('path')}: {failure.get('kind')}")

    summary130 = summaries.get("Sprint130")
    if summary130 is None:
        fail_reasons.append("Sprint130 summary missing")
    else:
        if summary130.get("fail_reasons", []) != []:
            fail_reasons.append(f"Sprint130 fail_reasons are not empty: {summary130.get('fail_reasons')}")
        prior_summaries = summary130.get("prior_summaries", [])
        prior_gate_status = {}
        for prior in prior_summaries if isinstance(prior_summaries, list) else []:
            if isinstance(prior, dict):
                prior_gate_status.update(prior.get("gate_status", {}))
        for gate in SPRINT130_EXPECTED_PRIOR_TRUE:
            if prior_gate_status.get(gate) is not True and claim_status.get(gate, {}).get("state") != "closed":
                fail_reasons.append(f"Sprint130 prior aggregate does not preserve {gate}=true")
        if summary130.get("os1_internal_readiness_closed") is not True:
            fail_reasons.append("Sprint130 OS1 internal readiness is not closed")
        if summary130.get("fin_internal_readiness_closed") is not True:
            fail_reasons.append("Sprint130 FIN internal readiness is not closed")

    external_acceptance = external_acceptance_state(summary130)
    if external_acceptance["present"] is not False:
        fail_reasons.append("external acceptance absence is not evidenced")

    clay_promotion = clay_promotion_state(summaries, repo_root)
    if clay_promotion["present"] is not False:
        fail_reasons.append("Clay Yang-Mills promotion false state is not evidenced")

    forbidden_marker_assertions = {
        sprint: summary.get("forbidden_incomplete_marker_assertion", {})
        for sprint, summary in summaries.items()
    }

    return {
        "audit_id": AUDIT_ID,
        "route_decision": "pass" if not fail_reasons else "fail-closed",
        "internal_gate_rows": internal_gate_rows,
        "claim_status": claim_status,
        "external_acceptance_absent": external_acceptance,
        "clay_promotion_false": clay_promotion,
        "prior_summary_paths": {label: path.as_posix() for label, path in PRIOR_SUMMARIES},
        "scanned_surfaces": {sprint: scan_paths(summary) for sprint, summary in summaries.items()},
        "forbidden_marker_assertions": forbidden_marker_assertions,
        "fail_reasons": fail_reasons,
    }


def render_report(summary: dict[str, Any]) -> str:
    lines = [
        "# Sprint 131 Final Claim Audit",
        "",
        f"- audit_id: `{summary['audit_id']}`",
        f"- route_decision: `{summary['route_decision']}`",
        f"- fail_reasons: `{len(summary['fail_reasons'])}`",
        "",
        "## Internal Claim State",
        "",
        "| Claim | Internal true | Source sprint | Evidence paths |",
        "| --- | --- | --- | --- |",
    ]
    for claim in EXPECTED_CLAIM_SOURCES:
        row = summary["claim_status"][claim]
        paths = sorted(
            {
                item.get("path", "")
                for item in row.get("evidence", [])
                if isinstance(item, dict) and item.get("path")
            }
        )
        lines.append(
            f"| {claim} | {row['state']} | {row['source_sprint']} | "
            f"{', '.join(paths) if paths else 'MISSING'} |"
        )

    ext = summary["external_acceptance_absent"]
    clay = summary["clay_promotion_false"]
    lines.extend(
        [
            "",
            "## Boundary State",
            "",
            f"- external acceptance present: `{str(ext['present']).lower()}`",
            f"- external acceptance evidence: `{json.dumps(ext.get('evidence', []), sort_keys=True)}`",
            f"- clayYangMillsPromoted present: `{str(clay['present']).lower()}`",
            f"- clayYangMillsPromoted flags: `{json.dumps(clay.get('flags', []), sort_keys=True)}`",
            "",
            "## Fail-Closed Scan",
            "",
        ]
    )
    for sprint, paths in summary["scanned_surfaces"].items():
        lines.append(f"- {sprint}: {len(paths)} scanned surfaces")
        for path in paths:
            lines.append(f"  - `{path}`")

    lines.extend(["", "## Fail Reasons", ""])
    if summary["fail_reasons"]:
        lines.extend(f"- {reason}" for reason in summary["fail_reasons"])
    else:
        lines.append("- none")
    lines.append("")
    return "\n".join(lines)


def main() -> int:
    args = parse_args()
    repo_root = args.repo_root.resolve()
    out_dir = args.out_dir
    if not out_dir.is_absolute():
        out_dir = repo_root / out_dir
    out_dir.mkdir(parents=True, exist_ok=True)

    summary = build_summary(repo_root)
    (out_dir / SUMMARY_NAME).write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    (out_dir / REPORT_NAME).write_text(render_report(summary), encoding="utf-8")
    print(json.dumps({"audit_id": AUDIT_ID, "fail_reasons": summary["fail_reasons"]}, sort_keys=True))
    return 0 if not summary["fail_reasons"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
