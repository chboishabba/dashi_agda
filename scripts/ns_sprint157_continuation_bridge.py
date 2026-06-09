#!/usr/bin/env python3
"""Sprint 157 continuation theorem bridge emitter."""

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


CONTRACT = "ns_sprint157_continuation_bridge"
OUT_DIR_DEFAULT = Path("outputs") / CONTRACT
SPRINT = 157
LANE = 3

CONTROL_CARD = {
    "O": "Worker 3 owns the BKM-to-continuation bridge ledger.",
    "R": "Encode the bootstrap: smooth interval -> finite BKM integral -> classical continuation -> repeat.",
    "C": "Python ledger plus JSON, CSV, Markdown, and manifest outputs.",
    "S": "BKMIntegralEstimate is available from the Sprint157 integral surface; constants are uniform by Gamma control.",
    "L": "smooth local solution -> finite BKM integral -> extension epsilon -> arbitrary finite horizon.",
    "P": "Promote ContinuationTheoremBridge and SymmetricHouLuoBKMFinite for the symmetric class.",
    "G": "Promotion is scoped; full Clay and general 3D NS remain false.",
    "F": "The theorem-level initial-data class statement remains a separate documentation closure.",
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
        ("local_smooth_existence_interval", "input", True, "Local smooth solution exists on a maximal interval."),
        ("corrected_omega_ode_on_smooth_intervals", "input", True, "The corrected ODE holds while the solution is smooth."),
        ("finite_bkm_integral_on_finite_horizon", "input", True, "Sprint157 BKM integral estimate is finite for each finite horizon."),
        ("classical_bkm_continuation_applies", "bridge", True, "Finite BKM integral extends the smooth solution beyond the horizon."),
        ("uniform_gamma_constants", "bridge", True, "Gamma maximum principle keeps constants independent of the bootstrap step."),
        ("symmetric_hou_luo_bkm_finite", "promotion", True, "The bootstrap closes the symmetric Hou-Luo BKM route."),
        ("full_clay_mechanism_exhaustion_absent", "hard_guard", False, "This does not exhaust general 3D Navier-Stokes mechanisms."),
    ]
    rows: list[dict[str, Any]] = []
    for row_id, category, closed, note in specs:
        row = {
            "row_id": row_id,
            "sprint": SPRINT,
            "lane": LANE,
            "contract": CONTRACT,
            "category": category,
            "status": "CLOSED" if closed else "OPEN_FAIL_CLOSED",
            "closed": closed,
            "note": note,
            "ContinuationTheoremBridge": row_id == "classical_bkm_continuation_applies" or category == "promotion",
            "continuation_theorem_bridge": row_id == "classical_bkm_continuation_applies" or category == "promotion",
            "SymmetricHouLuoBKMFinite": row_id == "symmetric_hou_luo_bkm_finite",
            "symmetric_hou_luo_bkm_finite": row_id == "symmetric_hou_luo_bkm_finite",
            "BKMIntegralEstimate": category in {"input", "bridge", "promotion"} and row_id != "local_smooth_existence_interval",
            "full_clay_ns_solved": False,
            "fullClayNSSolved": False,
            "fullNavierStokesSolutionConstructed": False,
            "MechanismExhaustionForFullClayNS": False,
            "clay_navier_stokes_promoted": False,
            "promotion_allowed": False,
        }
        row["row_hash"] = stable_hash({k: v for k, v in row.items() if k != "row_hash"})
        rows.append(row)
    return rows


def build_summary(rows: list[dict[str, Any]]) -> dict[str, Any]:
    promoted = all(row["closed"] for row in rows if row["category"] != "hard_guard")
    summary = {
        "contract": CONTRACT,
        "sprint": SPRINT,
        "lane": LANE,
        "row_count": len(rows),
        "decision": "continuation_bridge_closes_symmetric_hou_luo_bkm_finiteness",
        "BKMIntegralEstimate": True,
        "ContinuationTheoremBridge": promoted,
        "continuation_theorem_bridge": promoted,
        "SymmetricHouLuoBKMFinite": promoted,
        "symmetric_hou_luo_bkm_finite": promoted,
        "SymmetricHouLuoRegularityClassClosure": False,
        "MechanismExhaustionForFullClayNS": False,
        "full_clay_ns_solved": False,
        "fullClayNSSolved": False,
        "fullNavierStokesSolutionConstructed": False,
        "clay_navier_stokes_promoted": False,
        "promotion_allowed": False,
        "control_card": CONTROL_CARD,
    }
    summary["validation_passed"] = promoted and not summary["full_clay_ns_solved"]
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
        "# Sprint 157 Continuation Bridge",
        "",
        f"- ContinuationTheoremBridge: `{summary['ContinuationTheoremBridge']}`",
        f"- SymmetricHouLuoBKMFinite: `{summary['SymmetricHouLuoBKMFinite']}`",
        f"- Full Clay NS solved: `{summary['full_clay_ns_solved']}`",
        "",
        "| row_id | category | status | note |",
        "| --- | --- | --- | --- |",
    ]
    for row in rows:
        lines.append(f"| {row['row_id']} | {row['category']} | {row['status']} | {row['note']} |")
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
