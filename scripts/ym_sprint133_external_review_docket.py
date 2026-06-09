#!/usr/bin/env python3
"""Generate Sprint133 external Clay/CMI review docket rows.

This generator is deliberately fail-closed: repository-local Sprint131 and
Sprint132 evidence may document internal readiness and red-team/reproducibility
state, but it must not promote the Yang-Mills claim through external Clay/CMI
gates unless external evidence is actually present.
"""

from __future__ import annotations

import argparse
import json
import re
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Iterable


AUDIT_ID = "ym_sprint133_external_review_docket"
DEFAULT_OUT_DIR = Path("outputs/ym_sprint133_external_review_docket")
SUMMARY_NAME = f"{AUDIT_ID}.json"
ROWS_NAME = "external_review_docket_rows.json"
REPORT_NAME = f"{AUDIT_ID}.md"

SPRINT131_FINAL = Path(
    "outputs/ym_sprint131_final_claim_audit/ym_sprint131_final_claim_audit_summary.json"
)
SPRINT131_PACKET = Path(
    "outputs/ym_sprint131_submission_packet/ym_sprint131_submission_packet_summary.json"
)
SPRINT132_RED_TEAM = Path(
    "outputs/ym_sprint132_red_team_audit/ym_sprint132_red_team_audit_summary.json"
)
SPRINT132_ROWS = Path("outputs/ym_sprint132_red_team_audit/red_team_rows.json")
SPRINT132_BUNDLE = Path(
    "outputs/ym_sprint132_submission_bundle_index/ym_sprint132_submission_bundle_index.json"
)

SOURCE_EVIDENCE = {
    "sprint131_governance": SPRINT131_FINAL,
    "sprint131_submission_packet": SPRINT131_PACKET,
    "sprint132_red_team": SPRINT132_RED_TEAM,
    "sprint132_red_team_rows": SPRINT132_ROWS,
    "sprint132_repro_bundle": SPRINT132_BUNDLE,
}

EXTERNAL_GATES = (
    {
        "gate_id": "CLAY_EXTERNAL_REVIEW_ACCEPTANCE",
        "authority": "Clay Mathematics Institute",
        "external_gate": "Clay external review acceptance",
        "required_resolution": (
            "Obtain an external Clay Mathematics Institute review/acceptance "
            "record for the Yang-Mills existence and mass gap submission; "
            "repository-local internal audit evidence is insufficient."
        ),
    },
    {
        "gate_id": "CMI_PRIZE_VALIDATION",
        "authority": "Clay Mathematics Institute",
        "external_gate": "CMI Millennium Prize validation",
        "required_resolution": (
            "Obtain a CMI-recognized prize validation or public acceptance "
            "decision after external review; no Sprint131/Sprint132 artifact "
            "may stand in for that external governance decision."
        ),
    },
)

PROMOTION_TRUE_PATTERNS = (
    re.compile(r"(?m)^\s*clayYangMillsPromoted\s*=\s*true\s*$"),
    re.compile(r'"clayYangMillsPromoted"\s*:\s*true'),
    re.compile(r"\bclayYangMillsPromoted\s*:\s*true\b"),
)

SPRINT133_FORBIDDEN_MARKERS = (
    re.compile(r"\bpostulate\b", re.IGNORECASE),
    re.compile(r"\btodo\b", re.IGNORECASE),
    re.compile(r"\bstub\b", re.IGNORECASE),
    re.compile(r"\bskeleton\b", re.IGNORECASE),
    re.compile(r"\bdummy\b", re.IGNORECASE),
    re.compile(r"\bhole\b", re.IGNORECASE),
    re.compile(r"future\s*[- ]\s*proof", re.IGNORECASE),
    re.compile(re.escape("{" + "!") + r"|" + re.escape("!" + "}")),
)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--out-dir", type=Path, default=DEFAULT_OUT_DIR)
    return parser.parse_args()


def iter_values(value: Any) -> Iterable[Any]:
    yield value
    if isinstance(value, dict):
        for child in value.values():
            yield from iter_values(child)
    elif isinstance(value, list):
        for child in value:
            yield from iter_values(child)


def read_json(path: Path) -> tuple[Any | None, str | None]:
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError:
        return None, "missing"
    except json.JSONDecodeError as exc:
        return None, f"invalid JSON: {exc}"
    if payload in ({}, []):
        return payload, "empty JSON"
    return payload, None


def unique_paths(value: Any) -> list[str]:
    paths: set[str] = set()
    for item in iter_values(value):
        if isinstance(item, dict):
            path = item.get("path")
            if isinstance(path, str) and path:
                paths.add(path)
        elif isinstance(item, str) and (
            item.startswith("DASHI/") or item.startswith("outputs/")
        ):
            paths.add(item)
    return sorted(paths)


def line_for_offset(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def scan_paths_for_promotion_true(repo_root: Path, rel_paths: Iterable[str]) -> list[dict[str, Any]]:
    hits: list[dict[str, Any]] = []
    for rel_path in sorted(set(rel_paths)):
        path = repo_root / rel_path
        if not path.is_file():
            continue
        text = path.read_text(encoding="utf-8", errors="replace")
        for pattern in PROMOTION_TRUE_PATTERNS:
            for match in pattern.finditer(text):
                hits.append(
                    {
                        "path": rel_path,
                        "line": line_for_offset(text, match.start()),
                        "marker": "clayYangMillsPromoted=true",
                    }
                )
    return hits


def scan_sprint133_markers(repo_root: Path, out_dir: Path) -> list[dict[str, Any]]:
    paths = [repo_root / "scripts" / "ym_sprint133_external_review_docket.py"]
    if out_dir.exists():
        paths.extend(path for path in sorted(out_dir.rglob("*")) if path.is_file())
    hits: list[dict[str, Any]] = []
    for path in paths:
        if not path.is_file():
            continue
        text = path.read_text(encoding="utf-8", errors="replace")
        try:
            rel_path = path.relative_to(repo_root).as_posix()
        except ValueError:
            rel_path = path.as_posix()
        for pattern in SPRINT133_FORBIDDEN_MARKERS:
            for match in pattern.finditer(text):
                hits.append(
                    {
                        "path": rel_path,
                        "line": line_for_offset(text, match.start()),
                        "marker": match.group(0),
                    }
                )
    return hits


def bool_true_key_hits(payloads: dict[str, Any]) -> list[dict[str, Any]]:
    hits: list[dict[str, Any]] = []
    for source, payload in payloads.items():
        for item in iter_values(payload):
            if not isinstance(item, dict):
                continue
            for key, value in item.items():
                if key == "clayYangMillsPromoted" and value is True:
                    hits.append({"source": source, "key": key, "value": True})
                if key == "name" and value == "clayYangMillsPromoted" and item.get("value") is True:
                    hits.append({"source": source, "name": value, "value": True})
    return hits


def source_rel(rel_path: Path) -> str:
    return rel_path.as_posix()


def build_rows(source_paths: list[str]) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for gate in EXTERNAL_GATES:
        rows.append(
            {
                "gate_id": gate["gate_id"],
                "authority": gate["authority"],
                "external_gate": gate["external_gate"],
                "present": False,
                "external_gate_state": "absent",
                "repo_evidence_paths": source_paths,
                "required_resolution": gate["required_resolution"],
                "status": "resolved",
                "resolution_status": "resolved",
                "promotion": {
                    "clayYangMillsPromoted": False,
                    "no_false_promotion": "held_false",
                    "external_gate_promoted": False,
                },
            }
        )
    return rows


def render_markdown(summary: dict[str, Any], rows: list[dict[str, Any]]) -> str:
    lines = [
        "# Sprint133 External Review Docket",
        "",
        f"- Route decision: `{summary['route_decision']}`",
        f"- Fail closed: `{str(summary['fail_closed']).lower()}`",
        f"- clayYangMillsPromoted: `false`",
        "",
        "| Gate | Authority | Present | External gate state | Required resolution | Repo evidence paths |",
        "| --- | --- | --- | --- | --- | --- |",
    ]
    for row in rows:
        evidence = "<br>".join(f"`{path}`" for path in row["repo_evidence_paths"])
        lines.append(
            "| "
            + row["external_gate"]
            + " | "
            + row["authority"]
            + " | "
            + str(row["present"]).lower()
            + " | "
            + row["external_gate_state"]
            + " | "
            + row["required_resolution"]
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
    payloads: dict[str, Any] = {}
    for source, rel_path in SOURCE_EVIDENCE.items():
        payload, error = read_json(repo_root / rel_path)
        if error is not None:
            fail_reasons.append(f"{source} evidence at {source_rel(rel_path)} is {error}")
        if payload is not None:
            payloads[source] = payload

    required_sources = [source_rel(path) for path in SOURCE_EVIDENCE.values()]
    source_paths = sorted(set(required_sources + unique_paths(payloads)))
    missing_repo_evidence = [path for path in source_paths if not (repo_root / path).is_file()]
    if missing_repo_evidence:
        fail_reasons.append("repo evidence paths missing: " + ", ".join(missing_repo_evidence))

    if len(payloads) != len(SOURCE_EVIDENCE):
        fail_reasons.append("not all Sprint131 governance and Sprint132 red-team/repro outputs were consumed")

    sprint131_external = payloads.get("sprint131_governance", {}).get("external_acceptance_absent")
    if not isinstance(sprint131_external, dict) or sprint131_external.get("present") is not False:
        fail_reasons.append("Sprint131 governance does not record external acceptance present=false")

    sprint131_packet_boundary = payloads.get("sprint131_submission_packet", {}).get("external_boundary_row")
    if (
        not isinstance(sprint131_packet_boundary, dict)
        or sprint131_packet_boundary.get("status") != "absent"
        or sprint131_packet_boundary.get("closed") is not False
    ):
        fail_reasons.append("Sprint131 submission packet external boundary is not absent/closed=false")

    sprint132_summary = payloads.get("sprint132_red_team", {})
    if sprint132_summary.get("external_governance_present") is not False:
        fail_reasons.append("Sprint132 red-team output does not record external_governance_present=false")
    if sprint132_summary.get("external_governance", {}).get("state") != "absent":
        fail_reasons.append("Sprint132 red-team output does not record external governance state=absent")
    if sprint132_summary.get("promotion_true_detected") is True:
        fail_reasons.append("Sprint132 red-team output detected promotion true")
    if sprint132_summary.get("fail_reasons"):
        fail_reasons.append("Sprint132 red-team output contains fail_reasons")

    sprint132_rows = payloads.get("sprint132_red_team_rows", [])
    if not isinstance(sprint132_rows, list) or not sprint132_rows:
        fail_reasons.append("Sprint132 red-team rows are missing or empty")

    sprint132_bundle = payloads.get("sprint132_repro_bundle", {})
    if sprint132_bundle.get("fail_closed") is not True:
        fail_reasons.append("Sprint132 reproducibility bundle is not fail_closed=true")
    if sprint132_bundle.get("clayYangMillsPromoted") is True:
        fail_reasons.append("Sprint132 reproducibility bundle sets clayYangMillsPromoted=true")

    promotion_hits = bool_true_key_hits(payloads)
    promotion_hits.extend(scan_paths_for_promotion_true(repo_root, source_paths))
    if promotion_hits:
        fail_reasons.append("clayYangMillsPromoted=true detected in consumed evidence")

    rows = build_rows(source_paths)
    if not rows:
        fail_reasons.append("external review docket rows are empty")
    if any(row["present"] is not False or row["external_gate_state"] != "absent" for row in rows):
        fail_reasons.append("external docket contains a non-absent external gate")
    if any(not row["repo_evidence_paths"] for row in rows):
        fail_reasons.append("external docket row lacks repo evidence paths")
    if any(not row["required_resolution"] for row in rows):
        fail_reasons.append("external docket row lacks required_resolution text")
    if any(row["promotion"]["clayYangMillsPromoted"] is not False for row in rows):
        fail_reasons.append("external docket contains false promotion")

    route_decision = (
        "external_review_docket_emitted_external_gates_absent_no_promotion"
        if not fail_reasons
        else "fail_closed_external_review_docket_not_promoted"
    )
    summary = {
        "audit_id": AUDIT_ID,
        "generated_at_utc": datetime.now(timezone.utc).isoformat(timespec="seconds"),
        "route_decision": route_decision,
        "fail_closed": "pass" if not fail_reasons else "failed",
        "status": "resolved" if not fail_reasons else "fail_closed",
        "clayYangMillsPromoted": False,
        "source_evidence": {source: source_rel(path) for source, path in SOURCE_EVIDENCE.items()},
        "external_gate_count": len(rows),
        "external_review_docket_rows": rows,
        "missing_repo_evidence": missing_repo_evidence,
        "promotion_true_hits": promotion_hits,
        "fail_reasons": fail_reasons,
    }

    (out_dir / ROWS_NAME).write_text(json.dumps(rows, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    (out_dir / SUMMARY_NAME).write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    (out_dir / REPORT_NAME).write_text(render_markdown(summary, rows), encoding="utf-8")

    marker_hits = scan_sprint133_markers(repo_root, out_dir)
    if marker_hits:
        summary["fail_closed"] = False
        summary["status"] = "fail_closed"
        summary["route_decision"] = "fail_closed_external_review_docket_not_promoted"
        summary["sprint133_forbidden_marker_hits"] = marker_hits
        summary["fail_reasons"].append("forbidden Sprint133 markers detected")
        (out_dir / SUMMARY_NAME).write_text(
            json.dumps(summary, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
        (out_dir / REPORT_NAME).write_text(render_markdown(summary, rows), encoding="utf-8")
        return 1

    return 0 if not fail_reasons else 1


if __name__ == "__main__":
    raise SystemExit(main())
