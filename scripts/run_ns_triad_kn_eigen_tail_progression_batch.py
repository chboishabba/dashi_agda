#!/usr/bin/env python3
"""Run the NS triad K_N(A) eigen-tail adversary scan over multiple shells.

The runner fans out one scan/check pair per shell, writes all artifacts under
one output directory, and records a manifest with the commands, return codes,
paths, and parsed checker ok flags.
"""

from __future__ import annotations

import argparse
import json
import os
import shlex
import subprocess
import sys
import time
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
SCAN_SCRIPT = ROOT / "scripts" / "ns_triad_kn_eigen_tail_adversary_scan.py"
CHECK_SCRIPT = ROOT / "scripts" / "check_ns_triad_kn_eigen_tail_adversary_scan.py"

DEFAULT_OUTPUT_DIR = ROOT / "scripts" / "data" / "outputs" / "ns_boundary_pressure_geometric_20260621" / "ns_triad_kn_eigen_tail_adversary_batch"
DEFAULT_BACKEND = "cpu-matrix-free"
DEFAULT_LOBPCG_MAXITER = 40
DEFAULT_SAMPLE_COUNT = 4
DEFAULT_MIX_COUNT = 2
DEFAULT_PROFILE_SAMPLE_LIMIT = 6
DEFAULT_TRIAD_SAMPLE_LIMIT = 8
DEFAULT_MAX_PROFILES_PER_ROW = 4

TAIL_GRID_PRESETS: dict[str, dict[str, list[float] | list[int]]] = {
    "compact": {
        "c0_values": [0.25],
        "tail_cutoffs": [4, 5],
        "tail_etas": [0.25],
    },
    "default": {
        "c0_values": [0.10, 0.25],
        "tail_cutoffs": [4, 5, 6],
        "tail_etas": [0.25, 0.40],
    },
    "dense": {
        "c0_values": [0.05, 0.10, 0.25],
        "tail_cutoffs": [3, 4, 5, 6, 8],
        "tail_etas": [0.10, 0.25, 0.40, 0.60],
    },
}

TAIL_GRID_DETAIL_ALIASES = {
    "1": "compact",
    "2": "default",
    "3": "dense",
}

TAIL_GRID_SERIALIZATION_CHOICES = {"full", "summary", "none"}


def _json_text(payload: dict[str, Any], pretty: bool) -> str:
    if pretty:
        return json.dumps(payload, sort_keys=True, indent=2, allow_nan=False)
    return json.dumps(payload, sort_keys=True, separators=(",", ":"), allow_nan=False)


def _parse_csv_ints(value: str) -> list[int]:
    items: list[int] = []
    for raw_item in value.split(","):
        item = raw_item.strip()
        if item:
            items.append(int(item))
    if not items:
        raise argparse.ArgumentTypeError("must contain at least one shell")
    return items


def _parse_tail_grid_detail(value: str) -> str:
    normalized = value.strip().lower()
    normalized = TAIL_GRID_DETAIL_ALIASES.get(normalized, normalized)
    if normalized not in TAIL_GRID_PRESETS:
        raise argparse.ArgumentTypeError(
            "must be one of compact/default/dense or 1/2/3"
        )
    return normalized


def _parse_tail_grid_serialization(value: str) -> str:
    normalized = value.strip().lower()
    if normalized not in TAIL_GRID_SERIALIZATION_CHOICES:
        raise argparse.ArgumentTypeError("must be one of full/summary/none")
    return normalized


def _build_shell_list(shells_csv: str | None, repeated_shells: list[int] | None) -> list[int]:
    shells: list[int] = []
    if shells_csv is not None:
        shells.extend(_parse_csv_ints(shells_csv))
    if repeated_shells:
        shells.extend(int(shell) for shell in repeated_shells)
    if not shells:
        raise SystemExit("at least one shell is required")
    deduped = list(dict.fromkeys(shells))
    if any(shell < 0 for shell in deduped):
        raise SystemExit("shells must be nonnegative integers")
    return deduped


def _write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def _read_json_source(path: Path, stdout_text: str | None = None) -> dict[str, Any] | None:
    candidates: list[str] = []
    if stdout_text:
        candidates.append(stdout_text)
    if path.exists():
        candidates.append(path.read_text(encoding="utf-8"))
    for text in candidates:
        try:
            payload = json.loads(text)
        except json.JSONDecodeError:
            continue
        if isinstance(payload, dict):
            return payload
    return None


def _run_command(
    cmd: list[str],
    *,
    cwd: Path,
    env: dict[str, str],
    stdout_path: Path,
    stderr_path: Path,
) -> tuple[subprocess.CompletedProcess[str], int]:
    print("+ " + " ".join(shlex.quote(part) for part in cmd), flush=True)
    started = time.perf_counter()
    completed = subprocess.run(
        cmd,
        cwd=cwd,
        env=env,
        check=False,
        capture_output=True,
        text=True,
    )
    elapsed_ms = int(round((time.perf_counter() - started) * 1000.0))
    _write_text(stdout_path, completed.stdout)
    _write_text(stderr_path, completed.stderr)
    return completed, elapsed_ms


def _receipt_summary(payload: dict[str, Any] | None) -> dict[str, Any]:
    if not isinstance(payload, dict):
        return {
            "parsed": False,
            "status": None,
            "ok": None,
            "error_count": None,
        }
    return {
        "parsed": True,
        "status": payload.get("status"),
        "ok": payload.get("ok"),
        "error_count": payload.get("error_count"),
    }


def _scan_args(
    *,
    backend: str,
    shells: list[int],
    output_json: Path,
    sample_count: int,
    mix_count: int,
    profile_sample_limit: int,
    triad_sample_limit: int,
    max_profiles_per_row: int,
    lobpcg_maxiter: int,
    tail_grid_detail: str,
    tail_grid_serialization: str,
) -> list[str]:
    preset = TAIL_GRID_PRESETS[tail_grid_detail]
    cmd = [
        sys.executable,
        str(SCAN_SCRIPT),
        "--output-json",
        str(output_json),
        "--kn-backend",
        backend,
        "--sample-count",
        str(sample_count),
        "--mix-count",
        str(mix_count),
        "--profile-sample-limit",
        str(profile_sample_limit),
        "--triad-sample-limit",
        str(triad_sample_limit),
        "--max-profiles-per-row",
        str(max_profiles_per_row),
        "--lobpcg-maxiter",
        str(lobpcg_maxiter),
        "--c0-values",
        ",".join(str(value) for value in preset["c0_values"]),
        "--tail-cutoffs",
        ",".join(str(int(value)) for value in preset["tail_cutoffs"]),
        "--tail-etas",
        ",".join(str(value) for value in preset["tail_etas"]),
        "--tail-grid-detail",
        tail_grid_serialization,
    ]
    for shell in shells:
        cmd.extend(["--shell", str(shell)])
    return cmd


def _check_args(*, source_json: Path, output_json: Path) -> list[str]:
    return [
        sys.executable,
        str(CHECK_SCRIPT),
        "--source-json",
        str(source_json),
        "--output-json",
        str(output_json),
    ]


def _existing_ok_receipts(scan_json: Path, check_json: Path) -> tuple[dict[str, Any], dict[str, Any]] | None:
    if not scan_json.exists() or not check_json.exists():
        return None
    scan_payload = _read_json_source(scan_json)
    checker_payload = _read_json_source(check_json)
    if scan_payload is None or checker_payload is None:
        return None
    if _receipt_summary(checker_payload)["ok"] is not True:
        return None
    return scan_payload, checker_payload


def _run_shell(
    *,
    shell: int,
    backend: str,
    icd: str | None,
    out_dir: Path,
    sample_count: int,
    mix_count: int,
    profile_sample_limit: int,
    triad_sample_limit: int,
    max_profiles_per_row: int,
    lobpcg_maxiter: int,
    tail_grid_detail: str,
    tail_grid_serialization: str,
    skip_existing_ok: bool,
) -> dict[str, Any]:
    shell_dir = out_dir / f"shell_{shell:02d}"
    shell_dir.mkdir(parents=True, exist_ok=True)
    shell_started = time.perf_counter()

    scan_json = shell_dir / "ns_triad_kn_eigen_tail_adversary_scan.json"
    scan_stdout = shell_dir / "scan.stdout.json"
    scan_stderr = shell_dir / "scan.stderr.log"
    check_json = shell_dir / "check_ns_triad_kn_eigen_tail_adversary_scan.json"
    check_stdout = shell_dir / "check.stdout.json"
    check_stderr = shell_dir / "check.stderr.log"

    env = os.environ.copy()
    if icd:
        env["VK_ICD_FILENAMES"] = icd
    env["TRIAD_SAMPLE_LIMIT"] = str(triad_sample_limit)

    scan_cmd = _scan_args(
        backend=backend,
        shells=[shell],
        output_json=scan_json,
        sample_count=sample_count,
        mix_count=mix_count,
        profile_sample_limit=profile_sample_limit,
        triad_sample_limit=triad_sample_limit,
        max_profiles_per_row=max_profiles_per_row,
        lobpcg_maxiter=lobpcg_maxiter,
        tail_grid_detail=tail_grid_detail,
        tail_grid_serialization=tail_grid_serialization,
    )
    checker_cmd = _check_args(source_json=scan_json, output_json=check_json)

    existing_receipts = _existing_ok_receipts(scan_json, check_json) if skip_existing_ok else None
    if existing_receipts is not None:
        scan_payload, checker_payload = existing_receipts
        scan_summary = _receipt_summary(scan_payload)
        checker_summary = _receipt_summary(checker_payload)
        ok = bool(scan_summary["ok"] is True and checker_summary["ok"] is True)
        shell_elapsed_ms = int(round((time.perf_counter() - shell_started) * 1000.0))
        return {
            "shell": int(shell),
            "shell_dir": str(shell_dir),
            "shell_status": "reused_existing_ok",
            "shell_elapsed_ms": shell_elapsed_ms,
            "skipped_existing_ok": True,
            "scan_command": scan_cmd,
            "scan_status": "reused_existing_ok",
            "scan_elapsed_ms": 0,
            "scan": {
                "command": scan_cmd,
                "return_code": 0,
                "status": "reused_existing_ok",
                "elapsed_ms": 0,
                "stdout_path": str(scan_stdout),
                "stderr_path": str(scan_stderr),
                "receipt_path": str(scan_json),
                **scan_summary,
            },
            "check_command": checker_cmd,
            "checker_command": checker_cmd,
            "check_status": "reused_existing_ok",
            "checker_status": "reused_existing_ok",
            "checker_elapsed_ms": 0,
            "checker": {
                "command": checker_cmd,
                "return_code": 0,
                "status": "reused_existing_ok",
                "elapsed_ms": 0,
                "stdout_path": str(check_stdout),
                "stderr_path": str(check_stderr),
                "receipt_path": str(check_json),
                **checker_summary,
            },
            "ok": ok,
        }

    scan_completed, scan_elapsed_ms = _run_command(
        scan_cmd,
        cwd=ROOT,
        env=env,
        stdout_path=scan_stdout,
        stderr_path=scan_stderr,
    )
    scan_payload = _read_json_source(scan_json, scan_completed.stdout)

    checker_completed: subprocess.CompletedProcess[str] | None = None
    checker_payload: dict[str, Any] | None = None
    checker_elapsed_ms = 0
    if scan_json.exists():
        checker_completed, checker_elapsed_ms = _run_command(
            checker_cmd,
            cwd=ROOT,
            env=env,
            stdout_path=check_stdout,
            stderr_path=check_stderr,
        )
        checker_payload = _read_json_source(check_json, checker_completed.stdout)
    else:
        _write_text(check_stdout, "")
        _write_text(check_stderr, "scan receipt missing; checker skipped\n")

    scan_summary = _receipt_summary(scan_payload)
    checker_summary = _receipt_summary(checker_payload)
    ok = bool(
        scan_completed.returncode == 0
        and checker_completed is not None
        and checker_completed.returncode == 0
        and checker_summary["ok"] is True
    )
    shell_elapsed_ms = int(round((time.perf_counter() - shell_started) * 1000.0))
    scan_status = "completed" if scan_completed.returncode == 0 else "failed"
    checker_status = (
        "completed"
        if checker_completed is not None and checker_completed.returncode == 0 and checker_summary["ok"] is True
        else "skipped_scan_receipt_missing"
        if checker_completed is None
        else "failed"
    )

    return {
        "shell": int(shell),
        "shell_dir": str(shell_dir),
        "shell_status": "ok" if ok else "not_ok",
        "shell_elapsed_ms": shell_elapsed_ms,
        "skipped_existing_ok": False,
        "scan_command": scan_cmd,
        "scan_status": scan_status,
        "scan_elapsed_ms": scan_elapsed_ms,
        "scan": {
            "command": scan_cmd,
            "return_code": int(scan_completed.returncode),
            "status": scan_status,
            "elapsed_ms": scan_elapsed_ms,
            "stdout_path": str(scan_stdout),
            "stderr_path": str(scan_stderr),
            "receipt_path": str(scan_json),
            **scan_summary,
        },
        "check_command": checker_cmd,
        "checker_command": checker_cmd,
        "check_status": checker_status,
        "checker_status": checker_status,
        "checker_elapsed_ms": checker_elapsed_ms,
        "checker": {
            "command": checker_cmd,
            "return_code": None if checker_completed is None else int(checker_completed.returncode),
            "status": checker_status,
            "elapsed_ms": checker_elapsed_ms,
            "stdout_path": str(check_stdout),
            "stderr_path": str(check_stderr),
            "receipt_path": str(check_json),
            **checker_summary,
        },
        "ok": ok,
    }


def _summary(runs: list[dict[str, Any]]) -> dict[str, Any]:
    return {
        "shell_count": len(runs),
        "skipped_existing_ok_count": sum(1 for run in runs if run.get("skipped_existing_ok") is True),
        "ok_shell_count": sum(1 for run in runs if run.get("ok") is True),
        "scan_return_code_nonzero_count": sum(1 for run in runs if int(run["scan"]["return_code"]) != 0),
        "checker_return_code_nonzero_count": sum(
            1 for run in runs if run["checker"]["return_code"] is not None and int(run["checker"]["return_code"]) != 0
        ),
        "checker_ok_count": sum(1 for run in runs if run["checker"].get("ok") is True),
        "checker_error_count": sum(
            int(run["checker"]["error_count"] or 0) for run in runs if run["checker"].get("error_count") is not None
        ),
        "ok": all(bool(run.get("ok")) for run in runs),
    }


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--shells", type=str, default=None, help="Comma-separated shell list, e.g. 4,5,6.")
    parser.add_argument("--shell", dest="repeated_shells", action="append", type=int, default=None)
    parser.add_argument("--backend", choices=("cpu-matrix-free", "vulkan-matvec"), default=DEFAULT_BACKEND)
    parser.add_argument("--icd", type=str, default=None, help="Optional VK_ICD_FILENAMES value for Vulkan runs.")
    parser.add_argument("--lobpcg-maxiter", type=int, default=DEFAULT_LOBPCG_MAXITER)
    parser.add_argument("--sample-count", type=int, default=DEFAULT_SAMPLE_COUNT)
    parser.add_argument("--mix-count", type=int, default=DEFAULT_MIX_COUNT)
    parser.add_argument("--profile-sample-limit", type=int, default=DEFAULT_PROFILE_SAMPLE_LIMIT)
    parser.add_argument("--triad-sample-limit", type=int, default=DEFAULT_TRIAD_SAMPLE_LIMIT)
    parser.add_argument("--max-profiles-per-row", type=int, default=DEFAULT_MAX_PROFILES_PER_ROW)
    parser.add_argument(
        "--tail-grid-detail",
        type=_parse_tail_grid_detail,
        default="default",
        help="Tail-grid threshold preset: compact/default/dense or 1/2/3.",
    )
    parser.add_argument(
        "--tail-grid-serialization",
        type=_parse_tail_grid_serialization,
        default="summary",
        help="Per-profile tail-grid serialization passed to the scan: full/summary/none.",
    )
    parser.add_argument("--output-dir", type=Path, default=DEFAULT_OUTPUT_DIR)
    parser.add_argument("--skip-existing-ok", action="store_true")
    parser.add_argument("--pretty", action="store_true")
    return parser.parse_args()


def main() -> int:
    args = _parse_args()
    shells = _build_shell_list(args.shells, args.repeated_shells)
    output_dir = args.output_dir
    output_dir.mkdir(parents=True, exist_ok=True)

    runs = [
        _run_shell(
            shell=shell,
            backend=args.backend,
            icd=args.icd,
            out_dir=output_dir,
            sample_count=int(args.sample_count),
            mix_count=int(args.mix_count),
            profile_sample_limit=int(args.profile_sample_limit),
            triad_sample_limit=int(args.triad_sample_limit),
            max_profiles_per_row=int(args.max_profiles_per_row),
            lobpcg_maxiter=int(args.lobpcg_maxiter),
            tail_grid_detail=str(args.tail_grid_detail),
            tail_grid_serialization=str(args.tail_grid_serialization),
            skip_existing_ok=bool(args.skip_existing_ok),
        )
        for shell in shells
    ]

    manifest = {
        "script_name": "scripts/run_ns_triad_kn_eigen_tail_progression_batch.py",
        "contract": "run_ns_triad_kn_eigen_tail_progression_batch",
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "parameters": {
            "shells": shells,
            "backend": args.backend,
            "icd": args.icd,
            "lobpcg_maxiter": int(args.lobpcg_maxiter),
            "sample_count": int(args.sample_count),
            "mix_count": int(args.mix_count),
            "profile_sample_limit": int(args.profile_sample_limit),
            "triad_sample_limit": int(args.triad_sample_limit),
            "max_profiles_per_row": int(args.max_profiles_per_row),
            "tail_grid_detail": str(args.tail_grid_detail),
            "tail_grid_serialization": str(args.tail_grid_serialization),
            "output_dir": str(output_dir),
            "skip_existing_ok": bool(args.skip_existing_ok),
            "profile_adversary_coverage": {
                "shells": shells,
                "backend": args.backend,
                "icd": args.icd,
                "sample_count": int(args.sample_count),
                "mix_count": int(args.mix_count),
                "profile_sample_limit": int(args.profile_sample_limit),
                "max_profiles_per_row": int(args.max_profiles_per_row),
                "lobpcg_maxiter": int(args.lobpcg_maxiter),
                "tail_grid_detail": str(args.tail_grid_detail),
                "tail_grid_serialization": str(args.tail_grid_serialization),
            },
            "receipt_triad_sample_materialization": {
                "triad_sample_limit": int(args.triad_sample_limit),
            },
        },
        "runs": runs,
        "summary": _summary(runs),
    }

    manifest_path = output_dir / "ns_triad_kn_eigen_tail_adversary_batch_manifest.json"
    _write_text(manifest_path, _json_text(manifest, args.pretty) + "\n")
    print(_json_text(manifest, args.pretty))
    return 0 if manifest["summary"]["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
