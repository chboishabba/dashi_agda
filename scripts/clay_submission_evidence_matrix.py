#!/usr/bin/env python3
"""Emit a fail-closed Clay submission evidence matrix.

The matrix normalizes the existing theorem-agenda scripts for NS, YM, and
Paper8/UCT, then reflects known candidate audit surfaces when they are present.
Agenda marker validation is evidence that the repo tracks the blockers; it is
not evidence that the Clay proof is complete.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path
from typing import Any


REQUIRED_AGENDAS: dict[str, dict[str, Any]] = {
    "NS": {
        "script": "scripts/ns_missing_math_theorem_agenda.py",
        "row_key": "targets",
        "id_key": "theorem_id",
        "name_keys": ("theorem_name", "name", "title"),
        "terminal_keys": ("clay_promotion", "terminal_promotion", "promotion_allowed"),
        "args": ("--repo-root", "{repo_root}"),
    },
    "YM": {
        "script": "scripts/ym_missing_math_theorem_agenda.py",
        "row_key": "theorems",
        "id_key": "theorem_id",
        "name_keys": ("name", "theorem_name", "title"),
        "terminal_keys": ("clay_promotion", "terminal_promotion", "promotion_allowed"),
        "args": ("--repo-root", "{repo_root}"),
    },
    "Paper8/UCT": {
        "script": "scripts/uct_missing_math_theorem_agenda.py",
        "row_key": "theorem_targets",
        "id_key": "id",
        "name_keys": ("title", "name", "theorem_name"),
        "terminal_keys": ("terminal_promotion", "clay_promotion", "promotion_allowed"),
        "args": (),
    },
}

OPTIONAL_CANDIDATE_AUDITS: dict[str, tuple[dict[str, str], ...]] = {
    "NS": (
        {
            "name": "NS-A stationarity candidate audit",
            "script": "scripts/ns_stationarity_candidate_audit.py",
            "summary": "outputs/ns_stationarity_candidate_audit/ns_stationarity_candidate_audit_summary.json",
        },
        {
            "name": "NS-C kappa-bias candidate audit",
            "script": "scripts/ns_kappa_bias_candidate_audit.py",
            "summary": "outputs/ns_kappa_bias_candidate_audit/ns_kappa_bias_candidate_audit_summary.json",
        },
        {
            "name": "NS Sprint93 candidate source matrix audit",
            "script": "scripts/ns_sprint93_candidate_source_matrix_audit.py",
            "summary": "outputs/ns_sprint93_candidate_source_matrix_audit/ns_sprint93_candidate_source_matrix_audit_summary.json",
        },
    ),
    "YM": (
        {
            "name": "YM-A finite domination candidate audit",
            "script": "scripts/ym_finite_domination_candidate_audit.py",
            "summary": "outputs/ym_finite_domination_candidate_audit/ym_finite_domination_candidate_audit_summary.json",
        },
        {
            "name": "YM Sprint98 Clay statement boundary candidate audit",
            "script": "scripts/ym_sprint98_clay_statement_boundary_candidate_audit.py",
            "summary": "outputs/ym_sprint98_clay_statement_boundary_candidate/ym_sprint98_clay_statement_boundary_candidate_summary.json",
        },
        {
            "name": "YM Sprint112 map candidate reduction audit",
            "script": "scripts/ym_sprint112_map_candidate_reduction_audit.py",
            "summary": "outputs/ym_sprint112_map_candidate_reduction_audit/ym_sprint112_map_candidate_reduction_audit_summary.json",
        },
    ),
    "Paper8/UCT": (),
}


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--repo-root",
        type=Path,
        default=Path(__file__).resolve().parents[1],
        help="Repository root containing the agenda scripts.",
    )
    parser.add_argument(
        "--format",
        choices=("json", "md"),
        default="json",
        help="Output format. JSON is the default.",
    )
    return parser.parse_args(argv)


def run_agenda(repo_root: Path, domain: str, spec: dict[str, Any]) -> dict[str, Any]:
    script = repo_root / spec["script"]
    if not script.exists():
        raise RuntimeError(f"{domain}: required agenda script is missing: {spec['script']}")

    rendered_args = [
        str(repo_root) if arg == "{repo_root}" else arg for arg in spec.get("args", ())
    ]
    command = [sys.executable, str(script), *rendered_args]
    result = subprocess.run(
        command,
        cwd=repo_root,
        check=False,
        text=True,
        capture_output=True,
    )
    if result.returncode != 0:
        details = (result.stderr or result.stdout).strip()
        raise RuntimeError(
            f"{domain}: required agenda script failed with exit {result.returncode}: "
            f"{spec['script']}: {details}"
        )

    try:
        payload = json.loads(result.stdout)
    except json.JSONDecodeError as exc:
        raise RuntimeError(
            f"{domain}: required agenda script did not emit valid JSON: "
            f"{spec['script']}: {exc}"
        ) from exc

    rows = payload.get(spec["row_key"])
    if not isinstance(rows, list) or not rows:
        raise RuntimeError(
            f"{domain}: required agenda JSON missing non-empty {spec['row_key']!r} "
            f"from {spec['script']}"
        )
    return payload


def listify(value: Any) -> list[Any]:
    if value is None:
        return []
    if isinstance(value, list):
        return value
    if isinstance(value, tuple):
        return list(value)
    return [value]


def row_label(row: dict[str, Any], spec: dict[str, Any]) -> str:
    row_id = str(row.get(spec["id_key"], "unknown"))
    for key in spec["name_keys"]:
        value = row.get(key)
        if value:
            return f"{row_id} {value}"
    return row_id


def row_promoted(row: dict[str, Any], terminal_keys: tuple[str, ...]) -> bool:
    return any(row.get(key) is True for key in terminal_keys)


def authority_backed(payload: dict[str, Any], rows: list[dict[str, Any]]) -> bool:
    statuses = [str(row.get("status", "")).lower() for row in rows]
    if any("authority" in status for status in statuses):
        return True
    for row in rows:
        if listify(row.get("authority_inputs")):
            return True
        for option in listify(row.get("option_paths")):
            if isinstance(option, dict) and "authority" in str(option).lower():
                return True
    return False


def first_missing_math(row: dict[str, Any]) -> list[str]:
    for key in ("missing_estimates", "remaining_open_lemmas", "required_inputs"):
        values = [str(value) for value in listify(row.get(key)) if str(value)]
        if values:
            return values
    return [str(row.get("status", "unproved theorem blocker"))]


def summarize_candidate_audits(repo_root: Path, domain: str) -> list[dict[str, Any]]:
    audits: list[dict[str, Any]] = []
    for audit in OPTIONAL_CANDIDATE_AUDITS.get(domain, ()):
        script = repo_root / audit["script"]
        summary = repo_root / audit["summary"]
        summary_payload: dict[str, Any] | None = None
        summary_error: str | None = None
        if summary.exists():
            try:
                summary_payload = json.loads(summary.read_text(encoding="utf-8"))
            except json.JSONDecodeError as exc:
                summary_error = f"summary JSON is invalid: {exc}"
        audits.append(
            {
                "name": audit["name"],
                "script": audit["script"],
                "script_present": script.exists(),
                "summary": audit["summary"],
                "summary_present": summary.exists(),
                "summary_error": summary_error,
                "route_decision": (
                    summary_payload.get("route_decision")
                    if isinstance(summary_payload, dict)
                    else None
                ),
                "clay_promotion_detected": clay_promotion_detected(summary_payload),
                "reflection_status": (
                    "present"
                    if script.exists()
                    else f"optional candidate audit surface not present: {audit['script']}"
                ),
            }
        )
    return audits


def clay_promotion_detected(payload: Any) -> bool:
    if isinstance(payload, dict):
        for key, value in payload.items():
            lowered = str(key).lower()
            if lowered.startswith(("no_", "non_", "never_", "not_")):
                continue
            if "false" in lowered or "fail_closed" in lowered or "guard" in lowered:
                continue
            if "clay" in lowered and "promot" in lowered and value is True:
                return True
            if clay_promotion_detected(value):
                return True
    if isinstance(payload, list):
        return any(clay_promotion_detected(item) for item in payload)
    return False


def build_matrix(repo_root: Path) -> dict[str, Any]:
    repo_root = repo_root.resolve()
    rows_out: list[dict[str, Any]] = []
    agenda_payloads: dict[str, Any] = {}

    for domain, spec in REQUIRED_AGENDAS.items():
        payload = run_agenda(repo_root, domain, spec)
        agenda_payloads[domain] = payload
        targets = payload[spec["row_key"]]
        terminal_keys = tuple(spec["terminal_keys"])
        blockers = [
            target
            for target in targets
            if not row_promoted(target, terminal_keys)
            or listify(target.get("missing_estimates"))
            or "open" in str(target.get("status", "")).lower()
            or "locked" in str(target.get("status", "")).lower()
            or "false" in str(target.get("status", "")).lower()
            or "not_proved" in str(target.get("status", "")).lower()
        ]
        first = blockers[0] if blockers else targets[0]
        needed_math = first_missing_math(first)
        all_blockers_proved = not blockers and all(
            row_promoted(target, terminal_keys) for target in targets
        )
        candidate_audits = summarize_candidate_audits(repo_root, domain)
        optional_promotion = any(
            audit["clay_promotion_detected"] for audit in candidate_audits
        )

        rows_out.append(
            {
                "domain": domain,
                "submission_ready_as_reduction": False,
                "clay_eligible_proof": bool(all_blockers_proved and not optional_promotion),
                "authority_backed": authority_backed(payload, targets),
                "internal_proof_required": bool(blockers or needed_math),
                "first_blocker": row_label(first, spec),
                "needed_user_math": needed_math,
                "blocker_count": len(blockers),
                "all_blockers_proved": all_blockers_proved,
                "agenda_script": spec["script"],
                "agenda_ok": payload.get("ok") is True,
                "candidate_audits": candidate_audits,
            }
        )

    return {
        "schema": "dashi.clay_submission_evidence_matrix.v1",
        "ok": True,
        "fail_closed": True,
        "claim_policy": (
            "Clay eligible proof remains false unless every agenda blocker is proved; "
            "current agenda blockers are not proved."
        ),
        "domains": [row["domain"] for row in rows_out],
        "matrix": rows_out,
        "required_agenda_scripts": [
            spec["script"] for spec in REQUIRED_AGENDAS.values()
        ],
        "optional_candidate_audit_scripts": [
            audit["script"]
            for audits in OPTIONAL_CANDIDATE_AUDITS.values()
            for audit in audits
        ],
        "clay_eligible_domains": [
            row["domain"] for row in rows_out if row["clay_eligible_proof"]
        ],
        "agenda_payload_keys": {
            domain: sorted(payload.keys()) for domain, payload in agenda_payloads.items()
        },
    }


def render_md(payload: dict[str, Any]) -> str:
    lines = [
        "# Clay Submission Evidence Matrix",
        "",
        f"- fail_closed: `{str(payload['fail_closed']).lower()}`",
        f"- clay_eligible_domains: `{len(payload['clay_eligible_domains'])}`",
        "",
        "| domain | submission_ready_as_reduction | clay_eligible_proof | authority_backed | internal_proof_required | first_blocker | needed_user_math |",
        "| --- | --- | --- | --- | --- | --- | --- |",
    ]
    for row in payload["matrix"]:
        needed = "; ".join(row["needed_user_math"])
        lines.append(
            "| {domain} | `{submission}` | `{clay}` | `{authority}` | `{internal}` | {blocker} | {needed} |".format(
                domain=row["domain"],
                submission=str(row["submission_ready_as_reduction"]).lower(),
                clay=str(row["clay_eligible_proof"]).lower(),
                authority=str(row["authority_backed"]).lower(),
                internal=str(row["internal_proof_required"]).lower(),
                blocker=row["first_blocker"],
                needed=needed,
            )
        )
    return "\n".join(lines) + "\n"


def main(argv: list[str] | None = None) -> int:
    args = parse_args(argv)
    try:
        payload = build_matrix(args.repo_root)
    except RuntimeError as exc:
        print(f"clay_submission_evidence_matrix: {exc}", file=sys.stderr)
        return 2

    if args.format == "md":
        print(render_md(payload), end="")
    else:
        print(json.dumps(payload, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
