#!/usr/bin/env python3
"""Build the Sprint131 Yang-Mills submission packet from repository evidence."""

from __future__ import annotations

import json
import argparse
import re
import sys
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


DEFAULT_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_OUT_DIR = Path("outputs/ym_sprint131_submission_packet")
SUMMARY_NAME = "ym_sprint131_submission_packet_summary.json"
REPORT_NAME = "ym_sprint131_submission_packet.md"

SUMMARY_RELS = [
    Path("outputs/ym_sprint128_closure_audit/ym_sprint128_closure_audit_summary.json"),
    Path("outputs/ym_sprint129_mosco_spectral_audit/ym_sprint129_mosco_spectral_audit_summary.json"),
    Path("outputs/ym_sprint130_os_fin_audit/ym_sprint130_os_fin_audit_summary.json"),
]

AUDIT_MD_RELS = [
    Path("outputs/ym_sprint128_closure_audit/ym_sprint128_closure_audit.md"),
    Path("outputs/ym_sprint129_mosco_spectral_audit/ym_sprint129_mosco_spectral_audit.md"),
    Path("outputs/ym_sprint130_os_fin_audit/ym_sprint130_os_fin_audit.md"),
]

FORBIDDEN_MARKER_RE = re.compile(
    r"\b(postulate|todo|stub|skeleton|dummy|hole)\b|future\s+proof",
    re.IGNORECASE,
)
CLAY_TRUE_RE = re.compile(r"\bclayYangMillsPromoted\s*=\s*true\b")
EMPTY_DATA_RE = re.compile(r"^\s*data\s+([A-Za-z0-9_'.-]+).*?\bwhere\s*$")
DATA_OR_DECL_RE = re.compile(r"^\s*(data|record|module|[A-Za-z0-9_'.-]+\s*:)\b")


@dataclass(frozen=True)
class SurfaceFinding:
    path: str
    line: int
    kind: str
    text: str


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=DEFAULT_ROOT)
    parser.add_argument("--out-dir", type=Path, default=DEFAULT_OUT_DIR)
    return parser.parse_args()


def rel(root: Path, path: Path) -> str:
    return path.relative_to(root).as_posix()


def display_path(root: Path, path: Path) -> str:
    try:
        return rel(root, path)
    except ValueError:
        return path.as_posix()


def require_files(root: Path, paths: list[Path]) -> None:
    missing = [rel(root, path) for path in paths if not path.is_file()]
    if missing:
        raise SystemExit("missing required evidence files: " + ", ".join(missing))


def load_json(path: Path) -> dict[str, Any]:
    with path.open(encoding="utf-8") as handle:
        value = json.load(handle)
    if not isinstance(value, dict) or not value:
        raise SystemExit(f"required evidence JSON is empty or not an object: {rel(path)}")
    return value


def sprint_surfaces(root: Path) -> list[Path]:
    surfaces = sorted(
        (root / "DASHI").rglob("*.agda"),
        key=lambda path: rel(root, path),
    )
    selected = [
        path
        for path in surfaces
        if re.search(r"Sprint(?:128|129|130|131)", path.name)
    ]
    if not selected:
        raise SystemExit("no Sprint128-131 Agda surfaces found")
    return selected


def scan_surface(root: Path, path: Path) -> list[SurfaceFinding]:
    lines = path.read_text(encoding="utf-8").splitlines()
    findings: list[SurfaceFinding] = []
    for index, line in enumerate(lines, start=1):
        marker = FORBIDDEN_MARKER_RE.search(line)
        if marker:
            findings.append(SurfaceFinding(rel(root, path), index, "forbidden_marker", line.strip()))
        if CLAY_TRUE_RE.search(line):
            findings.append(SurfaceFinding(rel(root, path), index, "clayYangMillsPromoted_true", line.strip()))

    for index, line in enumerate(lines, start=1):
        match = EMPTY_DATA_RE.match(line)
        if not match:
            continue
        has_constructor = False
        for later in lines[index:]:
            if not later.strip() or later.lstrip().startswith("--"):
                continue
            if DATA_OR_DECL_RE.match(later):
                break
            has_constructor = True
            break
        if not has_constructor:
            findings.append(
                SurfaceFinding(rel(root, path), index, "empty_data_declaration", line.strip())
            )
    return findings


def fail_closed_scans_clean(summaries: list[dict[str, Any]]) -> bool:
    for summary in summaries:
        for scan in summary.get("fail_closed_scan", []):
            if scan.get("marker_hits"):
                return False
            if scan.get("empty_data_declarations"):
                return False
            if scan.get("clay_promotion_true_detected"):
                return False
    return True


def gate_rows(root: Path, summaries: list[dict[str, Any]], summary_paths: list[Path]) -> list[dict[str, Any]]:
    rows: dict[str, dict[str, Any]] = {}
    for summary in summaries:
        audit_id = summary["audit_id"]
        gate_status = summary.get("gate_status") or {}
        for gate, status in gate_status.items():
            if gate == "FIN" and audit_id != "ym_sprint130_os_fin_audit":
                continue
            key = f"{audit_id}:{gate}"
            flags = status.get("extracted_flags") or []
            evidence_paths = sorted({flag["path"] for flag in flags if flag.get("path")})
            if not evidence_paths:
                evidence_paths = sorted(
                    {
                        item["path"]
                        for item in status.get("evidence", [])
                        if isinstance(item, dict) and item.get("path")
                    }
                )
            if not evidence_paths:
                evidence_paths = [
                    rel(root, summary_paths[[path.name for path in summary_paths].index(f"{audit_id}_summary.json")])
                ]
            rows[key] = {
                "gate": gate,
                "source_audit": audit_id,
                "closed": bool(status.get("closed")),
                "kind": status.get("kind", "internal"),
                "required_flags": status.get("required_flags") or [],
                "false_required_flags": status.get("false_required_flags") or [],
                "missing_required_flags": status.get("missing_required_flags") or [],
                "evidence_paths": evidence_paths,
            }
    ordered = sorted(
        rows.values(),
        key=lambda row: (row["gate"] not in ["CC1", "WC1", "SC1", "SC2", "SC3", "MC1", "MC2", "MC3", "MC4", "SY1", "GG1", "OS1", "FIN"], row["gate"], row["source_audit"]),
    )
    if not ordered:
        raise SystemExit("no internal gate rows could be derived from audit summaries")
    return ordered


def artifact_map(root: Path, required_paths: list[Path], surfaces: list[Path]) -> list[dict[str, str]]:
    entries = []
    for path in required_paths + surfaces:
        category = "agda_surface" if path.suffix == ".agda" else "audit_evidence"
        entries.append({"path": rel(root, path), "category": category})
    return sorted(entries, key=lambda item: item["path"])


def external_boundary(summary130: dict[str, Any]) -> dict[str, Any]:
    assertion = summary130.get("external_acceptance_assertion") or {}
    flags = assertion.get("flags") or []
    if assertion.get("absent") is not True or not flags:
        raise SystemExit("external acceptance boundary evidence is missing or not absent")
    return {
        "boundary": "external_acceptance",
        "status": "absent",
        "closed": False,
        "promotion": "not_promoted",
        "evidence_flags": flags,
    }


def write_markdown(path: Path, packet: dict[str, Any]) -> None:
    lines = [
        "# Sprint131 Yang-Mills Submission Packet",
        "",
        "## Route Decision",
        "",
        f"- Decision: {packet['route_decision']}",
        f"- Generated UTC: {packet['generated_utc']}",
        "",
        "## Artifact Map",
        "",
        "| Path | Category |",
        "| --- | --- |",
    ]
    for item in packet["artifact_map"]:
        lines.append(f"| {item['path']} | {item['category']} |")

    lines.extend(["", "## Internal Gate Rows", "", "| Gate | Closed | Source Audit | Evidence Paths |", "| --- | --- | --- | --- |"])
    for row in packet["internal_gate_rows"]:
        paths = "<br>".join(row["evidence_paths"])
        lines.append(f"| {row['gate']} | {str(row['closed']).lower()} | {row['source_audit']} | {paths} |")

    boundary = packet["external_boundary_row"]
    flags = "<br>".join(f"{flag['path']}:{flag['name']}={str(flag['value']).lower()}" for flag in boundary["evidence_flags"])
    lines.extend([
        "",
        "## External Boundary Row",
        "",
        "| Boundary | Status | Promotion | Evidence |",
        "| --- | --- | --- | --- |",
        f"| {boundary['boundary']} | {boundary['status']} | {boundary['promotion']} | {flags} |",
        "",
        "## Validation",
        "",
        f"- Required evidence files present: {str(packet['validations']['required_evidence_files_present']).lower()}",
        f"- Sprint128-131 surfaces clean: {str(packet['validations']['sprint128_131_surfaces_clean']).lower()}",
        f"- clayYangMillsPromoted true absent: {str(packet['validations']['clay_promotion_true_absent']).lower()}",
    ])
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    args = parse_args()
    root = args.repo_root.resolve()
    out_dir = args.out_dir
    if not out_dir.is_absolute():
        out_dir = root / out_dir
    out_json = out_dir / SUMMARY_NAME
    out_md = out_dir / REPORT_NAME

    summary_paths = [root / path for path in SUMMARY_RELS]
    audit_md_paths = [root / path for path in AUDIT_MD_RELS]
    required_paths = summary_paths + audit_md_paths
    require_files(root, required_paths)
    summaries = [load_json(path) for path in summary_paths]
    summary_by_id = {summary["audit_id"]: summary for summary in summaries}
    surfaces = sprint_surfaces(root)
    require_files(root, surfaces)

    findings = [finding for surface in surfaces for finding in scan_surface(root, surface)]
    if findings:
        payload = [finding.__dict__ for finding in findings]
        raise SystemExit("Sprint128-131 Agda surface validation failed: " + json.dumps(payload, indent=2))
    if not fail_closed_scans_clean(summaries):
        raise SystemExit("audit fail-closed scans report forbidden markers, empty data, or Clay promotion")

    boundary = external_boundary(summary_by_id["ym_sprint130_os_fin_audit"])
    packet = {
        "packet_id": "ym_sprint131_submission_packet",
        "generated_utc": datetime.now(timezone.utc).replace(microsecond=0).isoformat(),
        "route_decision": "internal_submission_packet_built_external_acceptance_absent_no_clay_promotion",
        "artifact_map": artifact_map(root, required_paths, surfaces),
        "internal_gate_rows": gate_rows(root, summaries, summary_paths),
        "external_boundary_row": boundary,
        "validations": {
            "required_evidence_files_present": True,
            "sprint128_131_surfaces_clean": True,
            "audit_fail_closed_scans_clean": True,
            "clay_promotion_true_absent": True,
            "no_empty_sections": True,
        },
        "source_audits": [summary["audit_id"] for summary in summaries],
    }

    out_dir.mkdir(parents=True, exist_ok=True)
    out_json.write_text(json.dumps(packet, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    write_markdown(out_md, packet)
    print(display_path(root, out_json))
    print(display_path(root, out_md))
    return 0


if __name__ == "__main__":
    sys.exit(main())
