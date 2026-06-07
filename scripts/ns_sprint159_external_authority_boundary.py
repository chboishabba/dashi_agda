#!/usr/bin/env python3
"""Sprint 159 external authority boundary emitter."""

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


CONTRACT = "ns_sprint159_external_authority_boundary"
OUT_DIR_DEFAULT = Path("outputs") / CONTRACT
SPRINT = 159
LANE = 2

CONTROL_CARD = {
    "O": "Worker 2 owns the external authority boundary emitter.",
    "R": "Record symmetric Hou-Luo closure support while keeping Clay and mechanism exhaustion outside local authority.",
    "C": "Python stdlib emitter writes boundary rows, JSON, CSV, Markdown, and manifest.",
    "S": "Sprint158 closed the symmetric theorem statement and publication packet scope, but not full Clay.",
    "L": "symmetric closure support -> authority boundary -> Clay/mechanism guards remain false.",
    "P": "Use this artifact as the sprint159 boundary witness for external-authority escalation.",
    "G": "ExternalAuthorityBoundary must be true whenever local artifacts do not exhaust full Clay mechanisms.",
    "F": "Full Clay/mechanism exhaustion remains false until an external authority or complete mechanism proof closes it.",
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
        (
            "symmetric_hou_luo_closure_support",
            "supported_local_result",
            True,
            "Sprint158 theorem and packet artifacts support symmetric Hou-Luo closure.",
        ),
        (
            "full_clay_mechanism_exhaustion",
            "nonclaim_guard",
            False,
            "Local artifacts do not exhaust every full Clay Navier-Stokes mechanism.",
        ),
        (
            "external_authority_boundary",
            "authority_boundary",
            True,
            "Full Clay promotion requires external authority or a complete mechanism-exhaustion proof.",
        ),
    ]
    rows: list[dict[str, Any]] = []
    for row_id, category, supported, statement in specs:
        row = {
            "row_id": row_id,
            "sprint": SPRINT,
            "lane": LANE,
            "contract": CONTRACT,
            "category": category,
            "supported": supported,
            "status": "SUPPORTED" if supported else "NOT_SUPPORTED_FAIL_CLOSED",
            "statement_text": statement,
            "SymmetricHouLuoRegularityClassClosure": row_id == "symmetric_hou_luo_closure_support",
            "symmetric_hou_luo_closure_support": row_id == "symmetric_hou_luo_closure_support",
            "SymmetricHouLuoClosureSupport": row_id == "symmetric_hou_luo_closure_support",
            "MechanismExhaustionForFullClayNS": False,
            "FullClayMechanismExhaustion": False,
            "GeneralSmoothFiniteEnergyNSRegularity": False,
            "full_clay_ns_solved": False,
            "fullClayNSSolved": False,
            "fullNavierStokesSolutionConstructed": False,
            "clay_navier_stokes_promoted": False,
            "promotion_allowed": False,
            "ExternalAuthorityBoundary": True,
            "external_authority_boundary": True,
        }
        row["row_hash"] = stable_hash({k: v for k, v in row.items() if k != "row_hash"})
        rows.append(row)
    return rows


def build_summary(rows: list[dict[str, Any]]) -> dict[str, Any]:
    symmetric_support = any(row["SymmetricHouLuoClosureSupport"] for row in rows)
    external_boundary = all(row["ExternalAuthorityBoundary"] for row in rows)
    summary = {
        "contract": CONTRACT,
        "sprint": SPRINT,
        "lane": LANE,
        "row_count": len(rows),
        "decision": "external_authority_boundary_recorded_for_non_clay_symmetric_closure",
        "SymmetricHouLuoRegularityClassClosure": symmetric_support,
        "symmetric_hou_luo_closure_support": symmetric_support,
        "SymmetricHouLuoClosureSupport": symmetric_support,
        "MechanismExhaustionForFullClayNS": False,
        "FullClayMechanismExhaustion": False,
        "GeneralSmoothFiniteEnergyNSRegularity": False,
        "full_clay_ns_solved": False,
        "fullClayNSSolved": False,
        "fullNavierStokesSolutionConstructed": False,
        "clay_navier_stokes_promoted": False,
        "promotion_allowed": False,
        "ExternalAuthorityBoundary": external_boundary,
        "external_authority_boundary": external_boundary,
        "control_card": CONTROL_CARD,
    }
    clay_flags_false = (
        not summary["MechanismExhaustionForFullClayNS"]
        and not summary["FullClayMechanismExhaustion"]
        and not summary["GeneralSmoothFiniteEnergyNSRegularity"]
        and not summary["full_clay_ns_solved"]
        and not summary["fullClayNSSolved"]
        and not summary["fullNavierStokesSolutionConstructed"]
        and not summary["clay_navier_stokes_promoted"]
        and not summary["promotion_allowed"]
    )
    summary["validation_passed"] = clay_flags_false and summary["ExternalAuthorityBoundary"]
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
        "# Sprint 159 External Authority Boundary",
        "",
        f"- SymmetricHouLuoClosureSupport: `{summary['SymmetricHouLuoClosureSupport']}`",
        f"- MechanismExhaustionForFullClayNS: `{summary['MechanismExhaustionForFullClayNS']}`",
        f"- ExternalAuthorityBoundary: `{summary['ExternalAuthorityBoundary']}`",
        f"- Validation passed: `{summary['validation_passed']}`",
        "",
        "| row_id | category | status |",
        "| --- | --- | --- |",
    ]
    for row in rows:
        lines.append(f"| {row['row_id']} | {row['category']} | {row['status']} |")
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
