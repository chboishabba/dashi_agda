#!/usr/bin/env python3
"""Run sparse-Schur mixed-tail diagnostics across top-tail shell scales.

This is a narrow candidate-only scaling harness.  It reuses the canonical
mixed-tail decomposition receipt for each shell, then extracts the primary
tail-cutoff Rayleigh and sparse-Schur rows into a compact scaling table.
"""

from __future__ import annotations

import argparse
import json
import math
import subprocess
import sys
import time
from pathlib import Path
from typing import Any

from ns_triad_frame_stability_scan import AUTHORITY, OK_STATUS, PARTIAL_STATUS, _json_text  # type: ignore


SCRIPT_NAME = "scripts/ns_triad_kn_sparse_schur_scaling.py"
CONTRACT = "ns_triad_kn_sparse_schur_scaling"
ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_KN_SPARSE_SCHUR_SCALING"
SCHEMA_VERSION = "1.0.0"
DECOMPOSITION_SCRIPT = Path("scripts/ns_triad_kn_shell6_mixed_tail_decomposition.py")
DEFAULT_OUTPUT_DIR = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_kn_sparse_schur_scaling_20260624"
)


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, default=DEFAULT_OUTPUT_DIR)
    parser.add_argument("--shells", default="6,8,10", help="Comma-separated shell list.")
    parser.add_argument("--tail-offset", type=int, default=1, help="Use K=shell-tail_offset.")
    parser.add_argument("--tail-eta", type=float, default=0.25)
    parser.add_argument("--kn-backend", choices=("cpu-matrix-free", "vulkan-matvec"), default="cpu-matrix-free")
    parser.add_argument("--profile-builder", choices=("auto", "frame-surface", "streaming"), default="auto")
    parser.add_argument("--streaming-shell-threshold", type=int, default=10)
    parser.add_argument("--dense-schur-mode-limit", type=int, default=6000)
    parser.add_argument("--lobpcg-tol", type=float, default=1.0e-7)
    parser.add_argument("--lobpcg-maxiter", type=int, default=80)
    parser.add_argument("--block-size", type=int, default=3)
    parser.add_argument("--sparse-schur-tol", type=float, default=1.0e-8)
    parser.add_argument("--sparse-schur-maxiter", type=int, default=2000)
    parser.add_argument("--skip-existing-ok", action="store_true")
    parser.add_argument("--pretty", action="store_true")
    return parser.parse_args()


def _load_json(path: Path) -> dict[str, Any]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError(f"{path}: JSON root must be an object")
    return payload


def _finite_float(value: Any) -> float | None:
    if value is None or isinstance(value, bool):
        return None
    try:
        parsed = float(value)
    except (TypeError, ValueError):
        return None
    return parsed if math.isfinite(parsed) else None


def _parse_shells(text: str) -> list[int]:
    shells = []
    for part in text.split(","):
        part = part.strip()
        if not part:
            continue
        shells.append(int(part))
    if not shells:
        raise ValueError("--shells must contain at least one shell")
    return shells


def _receipt_ok(path: Path) -> bool:
    if not path.exists():
        return False
    try:
        payload = _load_json(path)
    except (OSError, json.JSONDecodeError, ValueError):
        return False
    return payload.get("status") == OK_STATUS


def _row_for_cutoff(rows: Any, cutoff: int) -> dict[str, Any]:
    if not isinstance(rows, list):
        return {}
    for row in rows:
        if isinstance(row, dict) and int(row.get("tail_cutoff", -1)) == int(cutoff):
            return row
    return {}


def _projection_component(rows: Any, component: str) -> dict[str, Any]:
    if not isinstance(rows, list):
        return {}
    for row in rows:
        if isinstance(row, dict) and row.get("component") == component:
            return row
    return {}


def _projection_squared_fraction(row: dict[str, Any]) -> float | None:
    value = _finite_float(row.get("squared_fraction"))
    if value is not None:
        return value
    return _finite_float(row.get("bkm_proxy_projection_fraction_sq"))


def _extract_summary(receipt_path: Path, *, shell: int, cutoff: int, eta: float, elapsed: float | None) -> dict[str, Any]:
    receipt = _load_json(receipt_path)
    result = receipt.get("result", {})
    if not isinstance(result, dict):
        result = {}
    split = _row_for_cutoff(result.get("component_rayleigh_splits"), cutoff)
    schur = _row_for_cutoff(result.get("schur_repair_rows"), cutoff)
    metrics = result.get("profile_metrics", {})
    tail_summary = result.get("tail_responsibility_summary", {})
    bkm_tail = _projection_component(
        result.get("bkm_stretching_proxy_projection_rows"),
        f"tail_K_ge_{cutoff}_component",
    )
    bkm_top = _projection_component(
        result.get("bkm_stretching_proxy_projection_rows"),
        f"top_shell_{shell}_component",
    )
    return {
        "shell": int(shell),
        "K": int(cutoff),
        "eta": float(eta),
        "status": receipt.get("status"),
        "detail_json": str(receipt_path),
        "elapsed_seconds": elapsed,
        "lambda_min": _finite_float(result.get("lambda_min")),
        "D": _finite_float(metrics.get("dissipation_proxy") if isinstance(metrics, dict) else None),
        "R_full": _finite_float(split.get("full_rayleigh_from_terms")),
        "R_finite": _finite_float(split.get("finite_only_rayleigh")),
        "R_tail": _finite_float(split.get("tail_only_rayleigh")),
        "R_cross": _finite_float(split.get("cross_term_rayleigh")),
        "tail_mass": _finite_float(split.get("tail_euclidean_mass")),
        "finite_mass": _finite_float(split.get("finite_euclidean_mass")),
        "cross_l_neg_fraction": _finite_float(split.get("cross_l_neg_fraction_of_full_numerator")),
        "eigen_tail_mass": _finite_float(
            tail_summary.get("eigen_tail_mass") if isinstance(tail_summary, dict) else None
        ),
        "worst_eigen_shell": tail_summary.get("worst_eigen_shell") if isinstance(tail_summary, dict) else None,
        "worst_eigen_shell_mass": _finite_float(
            tail_summary.get("worst_eigen_shell_mass") if isinstance(tail_summary, dict) else None
        ),
        "q_diag": _finite_float(schur.get("q_diag")),
        "q_coup": _finite_float(schur.get("q_coup")),
        "q_schur": _finite_float(schur.get("q_schur")),
        "q_schur_subtraction": _finite_float(schur.get("q_schur_subtraction")),
        "q_gap": _finite_float(schur.get("q_gap")),
        "q_gap_kind": schur.get("q_gap_kind"),
        "cg_info": schur.get("cg_info"),
        "cg_relative_residual": _finite_float(schur.get("cg_relative_residual")),
        "bkm_tail_projection_squared_fraction": _projection_squared_fraction(bkm_tail),
        "bkm_top_projection_squared_fraction": _projection_squared_fraction(bkm_top),
        "warnings": receipt.get("warnings", []),
    }


def _run_one(args: argparse.Namespace, *, shell: int, cutoff: int) -> tuple[dict[str, Any] | None, dict[str, Any]]:
    output_json = args.output_dir / f"shell{shell}_K{cutoff}_eta{int(round(float(args.tail_eta) * 1000)):03d}.json"
    output_md = output_json.with_suffix(".md")
    stdout_log = output_json.with_suffix(".stdout.log")
    stderr_log = output_json.with_suffix(".stderr.log")
    if bool(args.skip_existing_ok) and _receipt_ok(output_json):
        row = _extract_summary(output_json, shell=shell, cutoff=cutoff, eta=float(args.tail_eta), elapsed=None)
        return row, {
            "shell": shell,
            "K": cutoff,
            "status": "skipped",
            "skip_reason": "existing_ok",
            "output_json": str(output_json),
        }

    cmd = [
        sys.executable,
        str(DECOMPOSITION_SCRIPT),
        "--shell",
        str(shell),
        "--tail-cutoff",
        str(cutoff),
        "--tail-eta",
        str(float(args.tail_eta)),
        "--kn-backend",
        str(args.kn_backend),
        "--lobpcg-tol",
        str(float(args.lobpcg_tol)),
        "--lobpcg-maxiter",
        str(int(args.lobpcg_maxiter)),
        "--block-size",
        str(int(args.block_size)),
        "--profile-builder",
        str(args.profile_builder),
        "--streaming-shell-threshold",
        str(int(args.streaming_shell_threshold)),
        "--dense-schur-mode-limit",
        str(int(args.dense_schur_mode_limit)),
        "--sparse-schur",
        "--sparse-schur-tol",
        str(float(args.sparse_schur_tol)),
        "--sparse-schur-maxiter",
        str(int(args.sparse_schur_maxiter)),
        "--output-json",
        str(output_json),
        "--output-md",
        str(output_md),
        "--pretty",
    ]
    started = time.time()
    completed = subprocess.run(cmd, check=False, capture_output=True, text=True)
    elapsed = time.time() - started
    stdout_log.write_text(completed.stdout, encoding="utf-8")
    stderr_log.write_text(completed.stderr, encoding="utf-8")
    run = {
        "shell": shell,
        "K": cutoff,
        "status": OK_STATUS if completed.returncode == 0 else "error",
        "returncode": completed.returncode,
        "elapsed_seconds": elapsed,
        "output_json": str(output_json),
        "output_md": str(output_md),
        "stdout_log": str(stdout_log),
        "stderr_log": str(stderr_log),
    }
    if completed.returncode != 0:
        return None, run
    return _extract_summary(output_json, shell=shell, cutoff=cutoff, eta=float(args.tail_eta), elapsed=elapsed), run


def _markdown(payload: dict[str, Any]) -> str:
    def fmt(value: Any) -> str:
        if value is None:
            return "null"
        if isinstance(value, float):
            return f"{value:.6g}"
        return str(value)

    lines = [
        "# NS Triad K_N Sparse Schur Scaling",
        "",
        f"- status: `{payload['status']}`",
        f"- eta: `{fmt(payload['tail_eta'])}`",
        f"- tail offset: `{payload['tail_offset']}`",
        f"- rows: `{payload['row_count']}`",
        f"- failed rows: `{payload['failure_count']}`",
        "",
        "| N | K | D | R_full | R_tail | q_diag | q_coup | q_schur | q_gap | CG rel residual | BKM tail proj² |",
        "|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|",
    ]
    for row in payload["rows"]:
        lines.append(
            f"| {row['shell']} | {row['K']} | {fmt(row['D'])} | {fmt(row['R_full'])} | "
            f"{fmt(row['R_tail'])} | {fmt(row['q_diag'])} | {fmt(row['q_coup'])} | "
            f"{fmt(row['q_schur'])} | {fmt(row['q_gap'])} | {fmt(row['cg_relative_residual'])} | "
            f"{fmt(row['bkm_tail_projection_squared_fraction'])} |"
        )
    lines.extend(
        [
            "",
            "## Interpretation",
            "",
            payload["interpretation"],
            "",
        ]
    )
    return "\n".join(lines)


def main() -> int:
    args = _parse_args()
    args.output_dir.mkdir(parents=True, exist_ok=True)
    rows: list[dict[str, Any]] = []
    runs: list[dict[str, Any]] = []
    for shell in _parse_shells(str(args.shells)):
        cutoff = int(shell) - int(args.tail_offset)
        if cutoff <= 0:
            runs.append({"shell": shell, "K": cutoff, "status": "skipped", "skip_reason": "nonpositive_cutoff"})
            continue
        row, run = _run_one(args, shell=int(shell), cutoff=int(cutoff))
        runs.append(run)
        if row is not None:
            rows.append(row)

    failure_count = sum(1 for run in runs if run.get("status") not in {OK_STATUS, "skipped"})
    q_gaps = [float(row["q_gap"]) for row in rows if row.get("q_gap") is not None]
    r_tails = [float(row["R_tail"]) for row in rows if row.get("R_tail") is not None]
    interpretation = (
        "Candidate-only sparse Schur scaling scan. "
        f"The primary top-tail rows have min R_tail={min(r_tails) if r_tails else None} "
        f"and min q_gap={min(q_gaps) if q_gaps else None}. "
        "These values are telemetry for TailSubspaceCoercivity and SparseSchurTailRepair; "
        "they do not promote a theorem or Clay claim."
    )
    payload = {
        "script_name": SCRIPT_NAME,
        "contract": CONTRACT,
        "route_decision": ROUTE_DECISION,
        "schema_version": SCHEMA_VERSION,
        "authority": AUTHORITY,
        "status": OK_STATUS if failure_count == 0 else PARTIAL_STATUS,
        "candidate_only": True,
        "fail_closed": True,
        "theorem_promoted": False,
        "full_ns_promoted": False,
        "clay_promoted": False,
        "tail_eta": float(args.tail_eta),
        "tail_offset": int(args.tail_offset),
        "kn_backend": str(args.kn_backend),
        "row_count": len(rows),
        "failure_count": failure_count,
        "runs": runs,
        "rows": rows,
        "min_R_tail": min(r_tails) if r_tails else None,
        "min_q_gap": min(q_gaps) if q_gaps else None,
        "interpretation": interpretation,
    }
    output_json = args.output_dir / "summary.json"
    output_md = args.output_dir / "summary.md"
    output_json.write_text(_json_text(payload, bool(args.pretty)), encoding="utf-8")
    output_md.write_text(_markdown(payload), encoding="utf-8")
    print(_json_text(payload, bool(args.pretty)))
    return 0 if failure_count == 0 else 1


if __name__ == "__main__":
    raise SystemExit(main())
