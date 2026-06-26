#!/usr/bin/env python3
"""Create row-level manifests for mixed-tail K_N decomposition jobs.

The manifest is intentionally a scheduler artifact, not a solver.  One job is
one independent decomposition receipt, so callers can run CPU rows in parallel
and throttle Vulkan rows separately.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from ns_triad_frame_stability_scan import AUTHORITY, OK_STATUS, _json_text  # type: ignore


SCRIPT_NAME = "scripts/ns_triad_kn_grid_manifest.py"
CONTRACT = "ns_triad_kn_grid_manifest"
ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_KN_GRID_MANIFEST"
SCHEMA_VERSION = "1.0.0"

DEFAULT_OUTPUT_ROOT = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_kn_manifest_parallel_20260624"
)
DEFAULT_MANIFEST_JSON = DEFAULT_OUTPUT_ROOT / "manifest.json"
SUPPORTED_PROFILE_FAMILIES = ("forced-tail",)


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


def _parse_strings(values: list[str] | None, default: tuple[str, ...]) -> list[str]:
    if not values:
        return list(default)
    parsed: list[str] = []
    for value in values:
        for part in value.split(","):
            part = part.strip()
            if part:
                parsed.append(part)
    return parsed


def _eta_label(value: float) -> str:
    return f"{float(value):.3f}".replace(".", "p")


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--shell", dest="shells", action="append", default=None)
    parser.add_argument("--tail-cutoff", dest="tail_cutoffs", action="append", default=None)
    parser.add_argument("--tail-eta", dest="tail_etas", action="append", default=None)
    parser.add_argument("--d0", dest="d0_thresholds", action="append", default=None)
    parser.add_argument("--profile-family", dest="profile_families", action="append", default=None)
    parser.add_argument(
        "--backend",
        dest="backends",
        action="append",
        choices=("cpu-matrix-free", "vulkan-matvec"),
        default=None,
    )
    parser.add_argument("--output-root", type=Path, default=DEFAULT_OUTPUT_ROOT)
    parser.add_argument("--manifest-json", type=Path, default=DEFAULT_MANIFEST_JSON)
    parser.add_argument("--skip-empty-tail", action=argparse.BooleanOptionalAction, default=True)
    parser.add_argument("--lobpcg-tol", type=float, default=1.0e-7)
    parser.add_argument("--lobpcg-maxiter", type=int, default=80)
    parser.add_argument("--block-size", type=int, default=3)
    parser.add_argument("--gpu-matvec-checks", type=int, default=1)
    parser.add_argument(
        "--profile-builder",
        choices=("auto", "frame-surface", "streaming"),
        default="auto",
        help="Profile construction mode forwarded to the decomposition script.",
    )
    parser.add_argument(
        "--streaming-shell-threshold",
        type=int,
        default=10,
        help="In profile-builder=auto, stream profile construction at this shell and above.",
    )
    parser.add_argument(
        "--dense-schur-mode-limit",
        type=int,
        default=6000,
        help="Skip dense Schur diagnostics above this mode count; set <0 to force.",
    )
    parser.add_argument("--pretty", action="store_true")
    return parser.parse_args()


def _job_status(shell: int, cutoff: int, profile_family: str, skip_empty_tail: bool) -> tuple[str, list[str]]:
    warnings: list[str] = []
    if profile_family not in SUPPORTED_PROFILE_FAMILIES:
        warnings.append(f"unsupported profile_family={profile_family!r}; decomposition script currently supports forced-tail")
        return "unsupported_profile_family", warnings
    if bool(skip_empty_tail) and int(cutoff) > int(shell):
        warnings.append(f"empty tail subspace because K={int(cutoff)} exceeds shell N={int(shell)}")
        return "empty_tail_subspace", warnings
    return "pending", warnings


def main() -> int:
    args = _parse_args()
    shells = _parse_ints(args.shells, (6, 8))
    tail_cutoffs = _parse_ints(args.tail_cutoffs, (4, 5, 6))
    tail_etas = _parse_floats(args.tail_etas, (0.25, 0.40, 0.50))
    d0_thresholds = _parse_floats(args.d0_thresholds, (6.0, 8.0, 10.0, 14.0, 18.0))
    profile_families = _parse_strings(args.profile_families, ("forced-tail",))
    backends = _parse_strings(args.backends, ("cpu-matrix-free",))

    jobs: list[dict[str, Any]] = []
    for backend in backends:
        for shell in shells:
            for cutoff in tail_cutoffs:
                for eta in tail_etas:
                    for profile_family in profile_families:
                        status, warnings = _job_status(shell, cutoff, profile_family, bool(args.skip_empty_tail))
                        stem = (
                            f"{backend.replace('-', '_')}_shell_{shell:02d}_K_{cutoff:02d}_"
                            f"eta_{_eta_label(float(eta))}_{profile_family.replace('-', '_')}"
                        )
                        detail_dir = args.output_root / "receipts" / backend
                        job = {
                            "job_id": stem,
                            "status": status,
                            "shell": int(shell),
                            "K": int(cutoff),
                            "tail_cutoff": int(cutoff),
                            "eta": float(eta),
                            "tail_eta": float(eta),
                            "D0": d0_thresholds,
                            "d0_thresholds": d0_thresholds,
                            "profile_family": profile_family,
                            "backend": backend,
                            "output_json": str(detail_dir / f"{stem}.json"),
                            "output_md": str(detail_dir / f"{stem}.md"),
                            "stdout_log": str(detail_dir / f"{stem}.stdout.json"),
                            "stderr_log": str(detail_dir / f"{stem}.stderr.log"),
                            "warnings": warnings,
                        }
                        jobs.append(job)

    payload = {
        "script_name": SCRIPT_NAME,
        "contract": CONTRACT,
        "route_decision": ROUTE_DECISION,
        "schema_version": SCHEMA_VERSION,
        "authority": AUTHORITY,
        "status": OK_STATUS,
        "candidate_only": True,
        "fail_closed": True,
        "theorem_promoted": False,
        "full_ns_promoted": False,
        "clay_promoted": False,
        "shells": shells,
        "tail_cutoffs": tail_cutoffs,
        "tail_etas": tail_etas,
        "d0_thresholds": d0_thresholds,
        "profile_families": profile_families,
        "backends": backends,
        "skip_empty_tail": bool(args.skip_empty_tail),
        "solver_defaults": {
            "lobpcg_tol": float(args.lobpcg_tol),
            "lobpcg_maxiter": int(args.lobpcg_maxiter),
            "block_size": int(args.block_size),
            "gpu_matvec_checks": int(args.gpu_matvec_checks),
            "profile_builder": str(args.profile_builder),
            "streaming_shell_threshold": int(args.streaming_shell_threshold),
            "dense_schur_mode_limit": int(args.dense_schur_mode_limit),
        },
        "job_count": len(jobs),
        "jobs": jobs,
    }
    args.manifest_json.parent.mkdir(parents=True, exist_ok=True)
    args.manifest_json.write_text(_json_text(payload, bool(args.pretty)), encoding="utf-8")
    print(_json_text(payload, bool(args.pretty)))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
