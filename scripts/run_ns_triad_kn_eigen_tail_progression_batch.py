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
) -> subprocess.CompletedProcess[str]:
    print("+ " + " ".join(shlex.quote(part) for part in cmd), flush=True)
    completed = subprocess.run(
        cmd,
        cwd=cwd,
        env=env,
        check=False,
        capture_output=True,
        text=True,
    )
    _write_text(stdout_path, completed.stdout)
    _write_text(stderr_path, completed.stderr)
    return completed


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


def _run_shell(
    *,
    shell: int,
    backend: str,
    icd: str | None,
    out_dir: Path,
    sample_count: int,
    mix_count: int,
    profile_sample_limit: int,
    max_profiles_per_row: int,
    lobpcg_maxiter: int,
    tail_grid_detail: str,
    tail_grid_serialization: str,
) -> dict[str, Any]:
    shell_dir = out_dir / f"shell_{shell:02d}"
    shell_dir.mkdir(parents=True, exist_ok=True)

    scan_json = shell_dir / "ns_triad_kn_eigen_tail_adversary_scan.json"
    scan_stdout = shell_dir / "scan.stdout.json"
    scan_stderr = shell_dir / "scan.stderr.log"
    check_json = shell_dir / "check_ns_triad_kn_eigen_tail_adversary_scan.json"
    check_stdout = shell_dir / "check.stdout.json"
    check_stderr = shell_dir / "check.stderr.log"

    env = os.environ.copy()
    if icd:
        env["VK_ICD_FILENAMES"] = icd

    scan_cmd = _scan_args(
        backend=backend,
        shells=[shell],
        output_json=scan_json,
        sample_count=sample_count,
        mix_count=mix_count,
        profile_sample_limit=profile_sample_limit,
        max_profiles_per_row=max_profiles_per_row,
        lobpcg_maxiter=lobpcg_maxiter,
        tail_grid_detail=tail_grid_detail,
        tail_grid_serialization=tail_grid_serialization,
    )
    scan_completed = _run_command(
        scan_cmd,
        cwd=ROOT,
        env=env,
        stdout_path=scan_stdout,
        stderr_path=scan_stderr,
    )
    scan_payload = _read_json_source(scan_json, scan_completed.stdout)

    checker_completed: subprocess.CompletedProcess[str] | None = None
    checker_payload: dict[str, Any] | None = None
    checker_cmd: list[str] = []
    if scan_json.exists():
        checker_cmd = _check_args(source_json=scan_json, output_json=check_json)
        checker_completed = _run_command(
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

    return {
        "shell": int(shell),
        "shell_dir": str(shell_dir),
        "scan": {
            "command": scan_cmd,
            "return_code": int(scan_completed.returncode),
            "stdout_path": str(scan_stdout),
            "stderr_path": str(scan_stderr),
            "receipt_path": str(scan_json),
            **scan_summary,
        },
        "checker": {
            "command": checker_cmd,
            "return_code": None if checker_completed is None else int(checker_completed.returncode),
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
            max_profiles_per_row=int(args.max_profiles_per_row),
            lobpcg_maxiter=int(args.lobpcg_maxiter),
            tail_grid_detail=str(args.tail_grid_detail),
            tail_grid_serialization=str(args.tail_grid_serialization),
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
            "max_profiles_per_row": int(args.max_profiles_per_row),
            "tail_grid_detail": str(args.tail_grid_detail),
            "tail_grid_serialization": str(args.tail_grid_serialization),
            "output_dir": str(output_dir),
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
