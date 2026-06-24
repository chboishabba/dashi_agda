#!/usr/bin/env python3
"""Run mixed-tail decomposition receipts over an N/K grid.

This is a candidate-only wrapper around
``ns_triad_kn_shell6_mixed_tail_decomposition.py``.  It records one detailed
receipt per row and emits a compact aggregate table for tail-subspace
coercivity diagnostics.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path
from typing import Any

from ns_triad_frame_stability_scan import AUTHORITY, OK_STATUS, _json_text  # type: ignore


SCRIPT_NAME = "scripts/ns_triad_kn_mixed_tail_decomposition_grid.py"
CONTRACT = "ns_triad_kn_mixed_tail_decomposition_grid"
ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_KN_MIXED_TAIL_DECOMPOSITION_GRID"
SCHEMA_VERSION = "1.1.0"

DEFAULT_OUTPUT_DIR = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_kn_mixed_tail_decomposition_grid_20260623"
)
DEFAULT_OUTPUT_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_kn_mixed_tail_decomposition_grid_20260623.json"
)
DEFAULT_OUTPUT_MD = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_kn_mixed_tail_decomposition_grid_20260623.md"
)
DECOMPOSITION_SCRIPT = Path("scripts/ns_triad_kn_shell6_mixed_tail_decomposition.py")


def _parse_ints(values: list[str] | None, default: tuple[int, ...]) -> list[int]:
    if not values:
        return list(default)
    parsed: list[int] = []
    for value in values:
        for part in value.split(","):
            part = part.strip()
            if part:
                parsed.append(int(part))
    return parsed


def _parse_floats(values: list[str] | None, default: tuple[float, ...]) -> list[float]:
    if not values:
        return list(default)
    parsed: list[float] = []
    for value in values:
        for part in value.split(","):
            part = part.strip()
            if part:
                parsed.append(float(part))
    return parsed


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--shell", dest="shells", action="append", default=None)
    parser.add_argument("--tail-cutoff", dest="tail_cutoffs", action="append", default=None)
    parser.add_argument("--output-dir", type=Path, default=DEFAULT_OUTPUT_DIR)
    parser.add_argument("--output-json", type=Path, default=DEFAULT_OUTPUT_JSON)
    parser.add_argument("--output-md", type=Path, default=DEFAULT_OUTPUT_MD)
    parser.add_argument("--kn-backend", choices=("cpu-matrix-free", "vulkan-matvec"), default="vulkan-matvec")
    parser.add_argument("--gpu-matvec-checks", type=int, default=1)
    parser.add_argument("--tail-eta", dest="tail_etas", action="append", default=None)
    parser.add_argument("--d0", dest="d0_thresholds", action="append", default=None)
    parser.add_argument("--skip-existing-ok", action="store_true")
    parser.add_argument("--skip-empty-tail", action=argparse.BooleanOptionalAction, default=True)
    parser.add_argument("--lobpcg-tol", type=float, default=1.0e-7)
    parser.add_argument("--lobpcg-maxiter", type=int, default=80)
    parser.add_argument("--block-size", type=int, default=3)
    parser.add_argument("--pretty", action="store_true")
    return parser.parse_args()


def _component_for_cutoff(result: dict[str, Any], cutoff: int) -> dict[str, Any] | None:
    for row in result.get("component_rayleigh_splits", []):
        if int(row.get("tail_cutoff", -1)) == int(cutoff):
            return row
    return None


def _tail_worst_shell(result: dict[str, Any], cutoff: int) -> int | None:
    rows = [
        row
        for row in result.get("eigen_mass_by_shell", [])
        if int(row.get("shell", -1)) >= int(cutoff) and float(row.get("eigen_mass", 0.0)) > 0.0
    ]
    if not rows:
        return None
    return int(max(rows, key=lambda row: float(row.get("eigen_mass", 0.0)))["shell"])


def _summarize_row(payload: dict[str, Any], detail_json: Path, stdout_log: Path, stderr_log: Path) -> dict[str, Any]:
    result = payload["result"]
    cutoff = int(result["tail_responsibility_summary"]["tail_cutoff"])
    split = _component_for_cutoff(result, cutoff) or {}
    return {
        "shell": int(result["shell"]),
        "tail_cutoff": cutoff,
        "tail_eta": float(result.get("tail_eta", result["profile_id"].rsplit("_", 1)[-1])),
        "profile_id": result["profile_id"],
        "status": payload["status"],
        "lambda_min": result["lambda_min"],
        "R_full": split.get("full_rayleigh_from_terms"),
        "R_finite": split.get("finite_only_rayleigh"),
        "R_tail": split.get("tail_only_rayleigh"),
        "R_cross": split.get("cross_term_rayleigh"),
        "tail_mass": split.get("tail_euclidean_mass"),
        "finite_mass": split.get("finite_euclidean_mass"),
        "worst_shell": result["tail_responsibility_summary"].get("worst_eigen_shell"),
        "tail_only_worst_shell": _tail_worst_shell(result, cutoff),
        "profile_tail_mass": result["tail_responsibility_summary"].get("profile_tail_mass"),
        "D": result["profile_metrics"].get("dissipation_proxy"),
        "tail_touching_numerator_fraction": result["tail_responsibility_summary"].get(
            "tail_touching_rayleigh_numerator_fraction"
        ),
        "tail_touching_denominator_fraction": result["tail_responsibility_summary"].get(
            "tail_touching_rayleigh_denominator_fraction"
        ),
        "detail_json": str(detail_json),
        "stdout_log": str(stdout_log),
        "stderr_log": str(stderr_log),
        "warnings": payload.get("warnings", []),
    }


def _skipped_empty_tail_row(shell: int, cutoff: int, eta: float) -> dict[str, Any]:
    return {
        "shell": int(shell),
        "tail_cutoff": int(cutoff),
        "tail_eta": float(eta),
        "profile_id": f"forced_tail_K{int(cutoff)}_eta_{float(eta):.3f}",
        "status": "SKIPPED",
        "branch": "empty_tail_subspace",
        "lambda_min": None,
        "R_full": None,
        "R_finite": None,
        "R_tail": None,
        "R_cross": None,
        "tail_mass": 0.0,
        "finite_mass": 1.0,
        "worst_shell": None,
        "tail_only_worst_shell": None,
        "profile_tail_mass": 0.0,
        "D": None,
        "tail_touching_numerator_fraction": None,
        "tail_touching_denominator_fraction": None,
        "detail_json": None,
        "stdout_log": None,
        "stderr_log": None,
        "warnings": [f"skipped because tail cutoff K={int(cutoff)} exceeds shell N={int(shell)}"],
    }


def _attach_d0_flags(row: dict[str, Any], d0_thresholds: list[float]) -> dict[str, Any]:
    d_value = row.get("D")
    row["D0_flags"] = {
        f"{threshold:g}": (None if d_value is None else bool(float(d_value) <= float(threshold)))
        for threshold in d0_thresholds
    }
    return row


def _markdown(payload: dict[str, Any]) -> str:
    def fmt(value: Any) -> str:
        if value is None:
            return "null"
        if isinstance(value, float):
            return f"{value:.6g}"
        return str(value)

    lines = [
        "# NS Triad K_N Mixed-Tail Decomposition Grid",
        "",
        f"- status: `{payload['status']}`",
        f"- backend: `{payload['kn_backend']}`",
        f"- rows: `{len(payload['rows'])}`",
        "",
        "| N | K | eta | status | lambda | R_full | R_finite | R_tail | R_cross | tail mass | finite mass | worst shell | tail worst | profile tail | D |",
        "|---:|---:|---:|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|",
    ]
    for row in payload["rows"]:
        lines.append(
            f"| {row['shell']} | {row['tail_cutoff']} | {fmt(row['tail_eta'])} | {row['status']} | {fmt(row['lambda_min'])} | "
            f"{fmt(row['R_full'])} | {fmt(row['R_finite'])} | {fmt(row['R_tail'])} | "
            f"{fmt(row['R_cross'])} | {fmt(row['tail_mass'])} | {fmt(row['finite_mass'])} | "
            f"{fmt(row['worst_shell'])} | {fmt(row['tail_only_worst_shell'])} | "
            f"{fmt(row['profile_tail_mass'])} | {fmt(row['D'])} |"
        )
    lines.append("")
    return "\n".join(lines)


def main() -> int:
    args = _parse_args()
    shells = _parse_ints(args.shells, (4, 5, 6, 8))
    cutoffs = _parse_ints(args.tail_cutoffs, (3, 4, 5, 6))
    tail_etas = _parse_floats(args.tail_etas, (0.25,))
    d0_thresholds = _parse_floats(args.d0_thresholds, (6.0, 8.0, 10.0))
    args.output_dir.mkdir(parents=True, exist_ok=True)
    rows: list[dict[str, Any]] = []
    failures: list[dict[str, Any]] = []

    for shell in shells:
        for cutoff in cutoffs:
            for eta in tail_etas:
                if bool(args.skip_empty_tail) and int(cutoff) > int(shell):
                    rows.append(_attach_d0_flags(_skipped_empty_tail_row(shell, cutoff, eta), d0_thresholds))
                    continue
                eta_label = f"{float(eta):.3f}".replace(".", "p")
                stem = f"shell_{shell:02d}_K_{cutoff:02d}_eta_{eta_label}"
                detail_json = args.output_dir / f"{stem}.json"
                detail_md = args.output_dir / f"{stem}.md"
                stdout_log = args.output_dir / f"{stem}.stdout.json"
                stderr_log = args.output_dir / f"{stem}.stderr.log"
                if bool(args.skip_existing_ok) and detail_json.exists():
                    detail_payload = json.loads(detail_json.read_text(encoding="utf-8"))
                    if detail_payload.get("status") == OK_STATUS:
                        rows.append(
                            _attach_d0_flags(
                                _summarize_row(detail_payload, detail_json, stdout_log, stderr_log),
                                d0_thresholds,
                            )
                        )
                        continue
                cmd = [
                    sys.executable,
                    str(DECOMPOSITION_SCRIPT),
                    "--shell",
                    str(shell),
                    "--tail-cutoff",
                    str(cutoff),
                    "--tail-eta",
                    str(float(eta)),
                    "--kn-backend",
                    str(args.kn_backend),
                    "--gpu-matvec-checks",
                    str(int(args.gpu_matvec_checks)),
                    "--lobpcg-tol",
                    str(float(args.lobpcg_tol)),
                    "--lobpcg-maxiter",
                    str(int(args.lobpcg_maxiter)),
                    "--block-size",
                    str(int(args.block_size)),
                    "--output-json",
                    str(detail_json),
                    "--output-md",
                    str(detail_md),
                ]
                if args.pretty:
                    cmd.append("--pretty")
                completed = subprocess.run(cmd, check=False, capture_output=True, text=True)
                stdout_log.write_text(completed.stdout, encoding="utf-8")
                stderr_log.write_text(completed.stderr, encoding="utf-8")
                if completed.returncode != 0:
                    failures.append(
                        {
                            "shell": shell,
                            "tail_cutoff": cutoff,
                            "tail_eta": float(eta),
                            "returncode": completed.returncode,
                            "stderr_log": str(stderr_log),
                        }
                    )
                    continue
                detail_payload = json.loads(detail_json.read_text(encoding="utf-8"))
                rows.append(
                    _attach_d0_flags(_summarize_row(detail_payload, detail_json, stdout_log, stderr_log), d0_thresholds)
                )

    payload = {
        "script_name": SCRIPT_NAME,
        "contract": CONTRACT,
        "route_decision": ROUTE_DECISION,
        "schema_version": SCHEMA_VERSION,
        "authority": AUTHORITY,
        "status": OK_STATUS if not failures else "PARTIAL",
        "candidate_only": True,
        "fail_closed": True,
        "theorem_promoted": False,
        "full_ns_promoted": False,
        "clay_promoted": False,
        "kn_backend": str(args.kn_backend),
        "shells": shells,
        "tail_cutoffs": cutoffs,
        "tail_etas": tail_etas,
        "d0_thresholds": d0_thresholds,
        "skip_empty_tail": bool(args.skip_empty_tail),
        "skip_existing_ok": bool(args.skip_existing_ok),
        "row_count": len(rows),
        "failure_count": len(failures),
        "failures": failures,
        "rows": sorted(rows, key=lambda row: (int(row["shell"]), int(row["tail_cutoff"]), float(row["tail_eta"]))),
    }
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(_json_text(payload, bool(args.pretty)), encoding="utf-8")
    args.output_md.parent.mkdir(parents=True, exist_ok=True)
    args.output_md.write_text(_markdown(payload), encoding="utf-8")
    print(_json_text(payload, bool(args.pretty)))
    return 0 if not failures else 1


if __name__ == "__main__":
    raise SystemExit(main())
