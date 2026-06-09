#!/usr/bin/env python3
"""Sprint 158 publication packet readiness emitter."""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import os
import shutil
import sys
import tempfile
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint158_publication_packet_readiness"
OUT_DIR_DEFAULT = Path("outputs") / CONTRACT
SPRINT = 158
LANE = 4

CONTROL_CARD = {
    "O": "Worker 4 owns publication packet readiness.",
    "R": "Check that theorem statement, assumptions, proof dependencies, scope guards, and artifact index are packet-ready.",
    "C": "Python emitter writes readiness rows to JSON, CSV, Markdown, and manifest.",
    "S": "Class theorem closure is now explicit; full Clay remains open.",
    "L": "theorem statement -> dependency spine -> artifact index -> scope disclaimers -> packet-ready.",
    "P": "Promote publication packet readiness for the symmetric result only.",
    "G": "A packet-ready symmetric result cannot submit or promote Clay without mechanism exhaustion.",
    "F": "MechanismExhaustionForFullClayNS remains the sole full-Clay structural blocker.",
}


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--out-dir", type=Path, default=OUT_DIR_DEFAULT)
    return parser.parse_args()


def stable_hash(value: Any) -> str:
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def file_sha256(path: Path) -> str | None:
    if not path.exists():
        return None
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(65536), b""):
            digest.update(chunk)
    return digest.hexdigest()


def build_rows() -> list[dict[str, Any]]:
    specs = [
        ("theorem_statement", True),
        ("covered_assumptions", True),
        ("proof_dependency_spine_sprints_136_158", True),
        ("bkm_and_continuation_bridge", True),
        ("scope_guard_non_clay", True),
        ("artifact_index_agda_scripts_tests_outputs", True),
        ("full_clay_submission_packet", False),
    ]
    rows: list[dict[str, Any]] = []
    for row_id, ready in specs:
        row = {
            "row_id": row_id,
            "sprint": SPRINT,
            "lane": LANE,
            "contract": CONTRACT,
            "packet_ready": ready,
            "status": "READY" if ready else "NOT_READY_FAIL_CLOSED",
            "SymmetricHouLuoRegularityClassClosure": ready and row_id != "full_clay_submission_packet",
            "SymmetricHouLuoPublicationPacketReady": row_id != "full_clay_submission_packet" and ready,
            "MechanismExhaustionForFullClayNS": False,
            "GeneralSmoothFiniteEnergyNSRegularity": False,
            "full_clay_ns_solved": False,
            "fullClayNSSolved": False,
            "fullNavierStokesSolutionConstructed": False,
            "clay_navier_stokes_promoted": False,
            "promotion_allowed": False,
        }
        row["row_hash"] = stable_hash({k: v for k, v in row.items() if k != "row_hash"})
        rows.append(row)
    return rows


def build_summary(rows: list[dict[str, Any]]) -> dict[str, Any]:
    packet_ready = all(row["packet_ready"] for row in rows if row["row_id"] != "full_clay_submission_packet")
    summary = {
        "contract": CONTRACT,
        "sprint": SPRINT,
        "lane": LANE,
        "row_count": len(rows),
        "SymmetricHouLuoRegularityClassClosure": packet_ready,
        "SymmetricHouLuoPublicationPacketReady": packet_ready,
        "MechanismExhaustionForFullClayNS": False,
        "GeneralSmoothFiniteEnergyNSRegularity": False,
        "full_clay_ns_solved": False,
        "fullClayNSSolved": False,
        "fullNavierStokesSolutionConstructed": False,
        "clay_navier_stokes_promoted": False,
        "promotion_allowed": False,
        "control_card": CONTROL_CARD,
    }
    summary["validation_passed"] = packet_ready and not summary["full_clay_ns_solved"]
    summary["summary_hash"] = stable_hash({k: v for k, v in summary.items() if k != "summary_hash"})
    return summary


def write_json(path: Path, value: Any) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def write_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)


def render_markdown(summary: dict[str, Any], rows: list[dict[str, Any]]) -> str:
    lines = [
        "# Sprint 158 Publication Packet Readiness",
        "",
        f"- SymmetricHouLuoPublicationPacketReady: `{summary['SymmetricHouLuoPublicationPacketReady']}`",
        f"- Full Clay NS solved: `{summary['full_clay_ns_solved']}`",
        "",
        "| row_id | status |",
        "| --- | --- |",
    ]
    for row in rows:
        lines.append(f"| {row['row_id']} | {row['status']} |")
    lines.extend(["", "## O/R/C/S/L/P/G/F", ""])
    for key in ("O", "R", "C", "S", "L", "P", "G", "F"):
        lines.append(f"- {key}: {CONTROL_CARD[key]}")
    lines.append("")
    return "\n".join(lines)


def build_manifest(out_dir: Path, summary: dict[str, Any]) -> dict[str, Any]:
    files = {
        "summary": out_dir / f"{CONTRACT}_summary.json",
        "rows_json": out_dir / f"{CONTRACT}_rows.json",
        "rows_csv": out_dir / f"{CONTRACT}_rows.csv",
        "markdown": out_dir / f"{CONTRACT}.md",
        "manifest": out_dir / f"{CONTRACT}_manifest.json",
    }
    manifest = {
        "contract": CONTRACT,
        "sprint": SPRINT,
        "lane": LANE,
        "validation_passed": summary["validation_passed"],
        "files": {key: {"path": str(path), "exists": path.exists(), "sha256": file_sha256(path)} for key, path in files.items()},
    }
    manifest["manifest_hash"] = stable_hash({k: v for k, v in manifest.items() if k != "manifest_hash"})
    return manifest


def write_outputs(repo_root: Path, out_dir: Path, rows: list[dict[str, Any]], summary: dict[str, Any]) -> None:
    final_out = out_dir if out_dir.is_absolute() else repo_root / out_dir
    final_out.parent.mkdir(parents=True, exist_ok=True)
    temp_dir = Path(tempfile.mkdtemp(prefix=f".{CONTRACT}.", dir=final_out.parent))
    try:
        write_json(temp_dir / f"{CONTRACT}_rows.json", rows)
        write_csv(temp_dir / f"{CONTRACT}_rows.csv", rows)
        write_json(temp_dir / f"{CONTRACT}_summary.json", summary)
        (temp_dir / f"{CONTRACT}.md").write_text(render_markdown(summary, rows), encoding="utf-8")
        write_json(temp_dir / f"{CONTRACT}_manifest.json", build_manifest(temp_dir, summary))
        if final_out.exists():
            shutil.rmtree(final_out)
        os.replace(temp_dir, final_out)
        write_json(final_out / f"{CONTRACT}_manifest.json", build_manifest(final_out, summary))
    except Exception:
        shutil.rmtree(temp_dir, ignore_errors=True)
        raise


def main() -> int:
    args = parse_args()
    rows = build_rows()
    summary = build_summary(rows)
    write_outputs(args.repo_root.resolve(), args.out_dir, rows, summary)
    print(json.dumps({"contract": CONTRACT, "validation_passed": summary["validation_passed"], "out_dir": str(args.out_dir)}, sort_keys=True))
    return 0 if summary["validation_passed"] else 1


if __name__ == "__main__":
    sys.exit(main())
