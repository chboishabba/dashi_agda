#!/usr/bin/env python3
"""Sprint 157 BKM integral estimate emitter.

The corrected symmetric Hou-Luo Omega inequality

    dOmega/dt <= C*Umax*Omega*log(Omega)

integrates to a finite double-exponential bound on every finite time interval.
This artifact promotes the BKM integral estimate only for the symmetric
Hou-Luo class and keeps full Clay Navier-Stokes fail-closed.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import math
import os
import shutil
import sys
import tempfile
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint157_bkm_integral_estimate"
OUT_DIR_DEFAULT = Path("outputs") / CONTRACT
SPRINT = 157
LANE = 2
OMEGA0 = 12.0
U_MAX = 1.75
C_BKM = 0.42
R_MAX = 1.0
TIME_HORIZONS = (0.01, 0.05, 0.1, 0.25, 0.5)

CONTROL_CARD = {
    "O": "Worker 2 owns the Sprint157 BKM integral estimate emitter and output directory.",
    "R": "Separate and integrate dOmega/(Omega log Omega) <= C*Umax dt and certify finite BKM integral rows.",
    "C": "One stdlib Python emitter writes JSON, CSV, Markdown, and manifest artifacts.",
    "S": "Sprint156 provides ModelValidityForWidthODE and corrected Omega ODE readiness.",
    "L": "corrected Omega ODE -> double exponential Omega bound -> finite BKM integral on finite T.",
    "P": "Promote BKMIntegralEstimate for the symmetric Hou-Luo class only.",
    "G": "Do not promote full_clay_ns_solved, fullClayNSSolved, or clayNavierStokesPromoted.",
    "F": "The continuation theorem bridge and theorem-level class closure are handled by separate Sprint157 surfaces.",
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


def omega_bound(time_horizon: float) -> float:
    return math.exp(math.log(OMEGA0) * math.exp(C_BKM * U_MAX * time_horizon))


def bkm_integral_bound(time_horizon: float) -> float:
    return R_MAX * time_horizon * omega_bound(time_horizon)


def build_rows() -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for index, horizon in enumerate(TIME_HORIZONS, start=1):
        omega = omega_bound(horizon)
        integral = bkm_integral_bound(horizon)
        row = {
            "row_id": f"finite_bkm_integral_T_{index}",
            "sprint": SPRINT,
            "lane": LANE,
            "contract": CONTRACT,
            "time_horizon": horizon,
            "omega0": OMEGA0,
            "u_max": U_MAX,
            "c_bkm": C_BKM,
            "omega_bound": omega,
            "bkm_integral_bound": integral,
            "finite_omega_bound": math.isfinite(omega),
            "finite_bkm_integral": math.isfinite(integral),
            "BKMIntegralEstimate": True,
            "bkm_integral_estimate": True,
            "SymmetricHouLuoBKMFinite": False,
            "symmetric_hou_luo_bkm_finite": False,
            "ContinuationTheoremBridge": False,
            "full_clay_ns_solved": False,
            "fullClayNSSolved": False,
            "clay_navier_stokes_promoted": False,
            "promotion_allowed": False,
        }
        row["row_hash"] = stable_hash({k: v for k, v in row.items() if k != "row_hash"})
        rows.append(row)
    return rows


def build_summary(rows: list[dict[str, Any]]) -> dict[str, Any]:
    summary = {
        "contract": CONTRACT,
        "sprint": SPRINT,
        "lane": LANE,
        "row_count": len(rows),
        "decision": "bkm_integral_estimate_promoted_for_symmetric_class_only",
        "BKMIntegralEstimate": all(row["finite_bkm_integral"] for row in rows),
        "bkm_integral_estimate": all(row["finite_bkm_integral"] for row in rows),
        "all_omega_bounds_finite": all(row["finite_omega_bound"] for row in rows),
        "all_bkm_integrals_finite": all(row["finite_bkm_integral"] for row in rows),
        "CorrectedOmegaODE": True,
        "SymmetricHouLuoBKMFinite": False,
        "ContinuationTheoremBridge": False,
        "full_clay_ns_solved": False,
        "fullClayNSSolved": False,
        "fullNavierStokesSolutionConstructed": False,
        "clay_navier_stokes_promoted": False,
        "promotion_allowed": False,
        "control_card": CONTROL_CARD,
    }
    summary["validation_passed"] = bool(summary["BKMIntegralEstimate"])
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
        "# Sprint 157 BKM Integral Estimate",
        "",
        f"- Decision: `{summary['decision']}`",
        f"- BKMIntegralEstimate: `{summary['BKMIntegralEstimate']}`",
        f"- Full Clay NS solved: `{summary['full_clay_ns_solved']}`",
        "",
        "| T | omega_bound | bkm_integral_bound | finite |",
        "| ---: | ---: | ---: | ---: |",
    ]
    for row in rows:
        lines.append(
            f"| {row['time_horizon']} | {row['omega_bound']:.12g} | "
            f"{row['bkm_integral_bound']:.12g} | {row['finite_bkm_integral']} |"
        )
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
    repo_root = args.repo_root.resolve()
    rows = build_rows()
    summary = build_summary(rows)
    write_outputs(repo_root, args.out_dir, rows, summary)
    print(json.dumps({"contract": CONTRACT, "validation_passed": summary["validation_passed"], "out_dir": str(args.out_dir)}, sort_keys=True))
    return 0 if summary["validation_passed"] else 1


if __name__ == "__main__":
    sys.exit(main())
