#!/usr/bin/env python3
"""Run mixed-tail decomposition manifest jobs with CPU/GPU lane throttles."""

from __future__ import annotations

import argparse
import concurrent.futures
import json
import subprocess
import sys
import time
from pathlib import Path
from typing import Any

from ns_triad_frame_stability_scan import AUTHORITY, OK_STATUS, PARTIAL_STATUS, _json_text  # type: ignore


SCRIPT_NAME = "scripts/ns_triad_kn_run_manifest_parallel.py"
CONTRACT = "ns_triad_kn_run_manifest_parallel"
ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_KN_RUN_MANIFEST_PARALLEL"
SCHEMA_VERSION = "1.0.0"
DECOMPOSITION_SCRIPT = Path("scripts/ns_triad_kn_shell6_mixed_tail_decomposition.py")


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest-json", type=Path, required=True)
    parser.add_argument("--output-json", type=Path, default=None)
    parser.add_argument("--jobs", type=int, default=3, help="Maximum concurrent CPU lane jobs.")
    parser.add_argument("--gpu-jobs", type=int, default=1, help="Maximum concurrent Vulkan lane jobs.")
    parser.add_argument("--skip-existing-ok", action="store_true")
    parser.add_argument("--timeout-per-job", type=float, default=1800.0)
    parser.add_argument("--backend", choices=("cpu-matrix-free", "vulkan-matvec", "all"), default="all")
    parser.add_argument("--pretty", action="store_true")
    return parser.parse_args()


def _load_json(path: Path) -> dict[str, Any]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError(f"{path}: JSON root must be an object")
    return payload


def _is_existing_ok(job: dict[str, Any]) -> bool:
    output_json = Path(str(job["output_json"]))
    if not output_json.exists():
        return False
    try:
        payload = _load_json(output_json)
    except (OSError, json.JSONDecodeError, ValueError):
        return False
    return payload.get("status") == OK_STATUS


def _solver_defaults(manifest: dict[str, Any]) -> dict[str, Any]:
    defaults = manifest.get("solver_defaults")
    return defaults if isinstance(defaults, dict) else {}


def _skip_result(job: dict[str, Any], reason: str) -> dict[str, Any]:
    return {
        "job_id": job.get("job_id"),
        "status": "skipped",
        "skip_reason": reason,
        "backend": job.get("backend"),
        "shell": job.get("shell"),
        "K": job.get("K", job.get("tail_cutoff")),
        "eta": job.get("eta", job.get("tail_eta")),
        "profile_family": job.get("profile_family"),
        "output_json": job.get("output_json"),
        "stdout_log": job.get("stdout_log"),
        "stderr_log": job.get("stderr_log"),
        "warnings": job.get("warnings", []),
    }


def _run_one(job: dict[str, Any], defaults: dict[str, Any], timeout: float) -> dict[str, Any]:
    started = time.time()
    output_json = Path(str(job["output_json"]))
    output_md = Path(str(job["output_md"]))
    stdout_log = Path(str(job["stdout_log"]))
    stderr_log = Path(str(job["stderr_log"]))
    output_json.parent.mkdir(parents=True, exist_ok=True)
    output_md.parent.mkdir(parents=True, exist_ok=True)
    stdout_log.parent.mkdir(parents=True, exist_ok=True)
    stderr_log.parent.mkdir(parents=True, exist_ok=True)

    if job.get("status") == "empty_tail_subspace":
        return _skip_result(job, "empty_tail_subspace")
    if job.get("status") == "unsupported_profile_family":
        return _skip_result(job, "unsupported_profile_family")
    if job.get("profile_family", "forced-tail") != "forced-tail":
        return _skip_result(job, "unsupported_profile_family")

    cmd = [
        sys.executable,
        str(DECOMPOSITION_SCRIPT),
        "--shell",
        str(int(job["shell"])),
        "--tail-cutoff",
        str(int(job.get("tail_cutoff", job["K"]))),
        "--tail-eta",
        str(float(job.get("tail_eta", job["eta"]))),
        "--kn-backend",
        str(job["backend"]),
        "--gpu-matvec-checks",
        str(int(defaults.get("gpu_matvec_checks", 1))),
        "--lobpcg-tol",
        str(float(defaults.get("lobpcg_tol", 1.0e-7))),
        "--lobpcg-maxiter",
        str(int(defaults.get("lobpcg_maxiter", 80))),
        "--block-size",
        str(int(defaults.get("block_size", 3))),
        "--profile-builder",
        str(defaults.get("profile_builder", "auto")),
        "--streaming-shell-threshold",
        str(int(defaults.get("streaming_shell_threshold", 10))),
        "--dense-schur-mode-limit",
        str(int(defaults.get("dense_schur_mode_limit", 6000))),
        "--output-json",
        str(output_json),
        "--output-md",
        str(output_md),
        "--pretty",
    ]

    try:
        completed = subprocess.run(cmd, check=False, capture_output=True, text=True, timeout=float(timeout))
        stdout_log.write_text(completed.stdout, encoding="utf-8")
        stderr_log.write_text(completed.stderr, encoding="utf-8")
        status = OK_STATUS if completed.returncode == 0 else "error"
        error = None if completed.returncode == 0 else f"returncode={completed.returncode}"
    except subprocess.TimeoutExpired as exc:
        stdout_log.write_text(exc.stdout or "", encoding="utf-8")
        stderr_log.write_text(exc.stderr or "", encoding="utf-8")
        status = "timeout"
        error = f"timeout after {float(timeout):.1f}s"

    elapsed = time.time() - started
    return {
        "job_id": job.get("job_id"),
        "status": status,
        "error": error,
        "elapsed_seconds": elapsed,
        "backend": job.get("backend"),
        "shell": job.get("shell"),
        "K": job.get("K", job.get("tail_cutoff")),
        "eta": job.get("eta", job.get("tail_eta")),
        "D0": job.get("D0", job.get("d0_thresholds", [])),
        "d0_thresholds": job.get("d0_thresholds", job.get("D0", [])),
        "profile_family": job.get("profile_family"),
        "output_json": str(output_json),
        "output_md": str(output_md),
        "stdout_log": str(stdout_log),
        "stderr_log": str(stderr_log),
        "warnings": job.get("warnings", []),
    }


def _run_throttled_lanes(
    *,
    cpu_jobs: list[dict[str, Any]],
    gpu_jobs: list[dict[str, Any]],
    cpu_workers: int,
    gpu_workers: int,
    defaults: dict[str, Any],
    timeout: float,
) -> list[dict[str, Any]]:
    results: list[dict[str, Any]] = []
    executors: list[concurrent.futures.ThreadPoolExecutor] = []
    future_map: dict[concurrent.futures.Future[dict[str, Any]], dict[str, Any]] = {}
    try:
        if cpu_jobs:
            cpu_executor = concurrent.futures.ThreadPoolExecutor(max_workers=max(1, int(cpu_workers)))
            executors.append(cpu_executor)
            for job in cpu_jobs:
                future_map[cpu_executor.submit(_run_one, job, defaults, timeout)] = job
        if gpu_jobs:
            gpu_executor = concurrent.futures.ThreadPoolExecutor(max_workers=max(1, int(gpu_workers)))
            executors.append(gpu_executor)
            for job in gpu_jobs:
                future_map[gpu_executor.submit(_run_one, job, defaults, timeout)] = job
        for future in concurrent.futures.as_completed(future_map):
            results.append(future.result())
    finally:
        for executor in executors:
            executor.shutdown(wait=True)
    return results


def main() -> int:
    args = _parse_args()
    manifest = _load_json(args.manifest_json)
    defaults = _solver_defaults(manifest)
    jobs = [job for job in manifest.get("jobs", []) if isinstance(job, dict)]
    if args.backend != "all":
        jobs = [job for job in jobs if job.get("backend") == args.backend]

    skipped_existing: list[dict[str, Any]] = []
    runnable: list[dict[str, Any]] = []
    for job in jobs:
        if bool(args.skip_existing_ok) and _is_existing_ok(job):
            skipped_existing.append(_skip_result(job, "existing_ok"))
        else:
            runnable.append(job)

    cpu_jobs = [job for job in runnable if job.get("backend") == "cpu-matrix-free"]
    gpu_jobs = [job for job in runnable if job.get("backend") == "vulkan-matvec"]
    other_jobs = [job for job in runnable if job.get("backend") not in {"cpu-matrix-free", "vulkan-matvec"}]

    lane_results = _run_throttled_lanes(
        cpu_jobs=cpu_jobs,
        gpu_jobs=gpu_jobs,
        cpu_workers=max(1, int(args.jobs)),
        gpu_workers=max(1, int(args.gpu_jobs)),
        defaults=defaults,
        timeout=float(args.timeout_per_job),
    )
    other_results = [_skip_result(job, "unsupported_backend") for job in other_jobs]

    runs = sorted(
        skipped_existing + lane_results + other_results,
        key=lambda row: str(row.get("job_id", "")),
    )
    failure_count = sum(1 for row in runs if row.get("status") not in {OK_STATUS, "skipped"})
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
        "manifest_json": str(args.manifest_json),
        "skip_existing_ok": bool(args.skip_existing_ok),
        "jobs": int(args.jobs),
        "gpu_jobs": int(args.gpu_jobs),
        "timeout_per_job": float(args.timeout_per_job),
        "run_count": len(runs),
        "failure_count": failure_count,
        "runs": runs,
    }

    output_json = args.output_json or args.manifest_json.with_name("manifest_run_summary.json")
    output_json.parent.mkdir(parents=True, exist_ok=True)
    output_json.write_text(_json_text(payload, bool(args.pretty)), encoding="utf-8")
    print(_json_text(payload, bool(args.pretty)))
    return 0 if failure_count == 0 else 1


if __name__ == "__main__":
    raise SystemExit(main())
