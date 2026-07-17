#!/usr/bin/env python3
"""Run a selected stage of the local NS perturbation manifest sequentially.

This runner intentionally executes one finite-Galerkin candidate at a time.
It is a bounded empirical scheduler, not an optimiser and not theorem
authority.  The manifest's explicit stages provide the only promotion path:
static -> .05T -> .10T -> .25T.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time
from typing import Any


DEFAULT_MANIFEST = Path(
    "scripts/data/outputs/ns_interaction_closure_production/"
    "ns_profile_positive_chi_local_perturbation_manifest.json"
)
DEFAULT_OUTPUT = Path(
    "scripts/data/outputs/ns_interaction_closure_production/"
    "ns_profile_positive_chi_local_perturbation_runs"
)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    parser.add_argument("--stage", choices=("static", "short", "medium", "parabolic"), required=True)
    parser.add_argument("--ids", required=True, help="comma-separated manifest IDs; explicit selection prevents accidental full GPU sweeps")
    parser.add_argument("--output-dir", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--python", default=sys.executable)
    parser.add_argument("--audit-script", type=Path, default=Path("scripts/ns_normalized_profile_quotient_audit.py"))
    return parser.parse_args()


def stage_arguments(entry: dict[str, Any], stage: str) -> list[str]:
    arguments = list(entry["stage_a_static_arguments"])
    if stage == "short":
        arguments += entry["stage_b_short_residence_additions"]
    elif stage == "medium":
        arguments += entry["stage_c_medium_residence_additions"]
    elif stage == "parabolic":
        arguments += entry["stage_d_parabolic_window_additions"]
    return arguments


def atomic_text(path: Path, text: str) -> None:
    """Write one durable sidecar without exposing a partial final file."""
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(
        mode="w", encoding="utf-8", dir=path.parent,
        prefix=f".{path.name}.", suffix=".partial", delete=False,
    ) as handle:
        temporary = Path(handle.name)
        handle.write(text)
        handle.flush()
        os.fsync(handle.fileno())
    try:
        os.replace(temporary, path)
    finally:
        if temporary.exists():
            temporary.unlink()


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def execution_status(
    identity: str, stage: str, command: list[str], output_json: Path,
    stdout: Path, stderr: Path, checksum_path: Path,
    state: str, returncode: int | None = None, validation_error: str | None = None,
    checksum: str | None = None,
) -> dict[str, Any]:
    """Build the status sidecar used as the execution authority.

    A ``running`` record is deliberately durable before the child starts.  If
    the host later kills the runner, that status plus partial files proves an
    incomplete attempt rather than looking like a missing or successful one.
    """
    return {
        "contract": "durable_local_perturbation_execution_receipt_nonpromoting",
        "id": identity,
        "stage": stage,
        "state": state,
        "recorded_unix_time": time.time(),
        "command": command,
        "returncode": returncode,
        "receipt_promoted": state == "promoted",
        "validation_error": validation_error,
        "artifacts": {
            "receipt": str(output_json),
            "stdout": str(stdout),
            "stderr": str(stderr),
            "receipt_sha256_file": str(checksum_path) if checksum is not None else None,
            "receipt_sha256": checksum,
        },
    }


def main() -> None:
    args = parse_args()
    manifest = json.loads(args.manifest.read_text())
    requested = [item for item in args.ids.split(",") if item]
    indexed = {entry["id"]: entry for entry in manifest["entries"]}
    missing = [item for item in requested if item not in indexed]
    if missing:
        raise ValueError(f"unknown manifest IDs: {', '.join(missing)}")
    args.output_dir.mkdir(parents=True, exist_ok=True)
    rows: list[dict[str, Any]] = []
    for ordinal, identity in enumerate(requested, start=1):
        entry = indexed[identity]
        output_json = args.output_dir / f"{identity}_{args.stage}.json"
        stdout = args.output_dir / f"{identity}_{args.stage}.stdout"
        stderr = args.output_dir / f"{identity}_{args.stage}.stderr"
        status = args.output_dir / f"{identity}_{args.stage}.status.json"
        checksum_path = args.output_dir / f"{identity}_{args.stage}.sha256"
        partial_json = output_json.with_name(f".{output_json.name}.runner.partial")
        partial_stdout = stdout.with_name(f".{stdout.name}.runner.partial")
        partial_stderr = stderr.with_name(f".{stderr.name}.runner.partial")
        command = [args.python, str(args.audit_script), *stage_arguments(entry, args.stage), "--output-json", str(partial_json)]
        print(f"[{ordinal}/{len(requested)}] {identity} stage={args.stage}", flush=True)
        atomic_text(status, json.dumps(execution_status(
            identity, args.stage, command, output_json, stdout, stderr, checksum_path, "running",
        ), indent=2, sort_keys=True) + "\n")
        completed: subprocess.CompletedProcess[str] | None = None
        interrupted: BaseException | None = None
        try:
            with partial_stdout.open("w", encoding="utf-8") as stdout_handle, partial_stderr.open("w", encoding="utf-8") as stderr_handle:
                completed = subprocess.run(command, text=True, stdout=stdout_handle, stderr=stderr_handle)
                stdout_handle.flush()
                stderr_handle.flush()
                os.fsync(stdout_handle.fileno())
                os.fsync(stderr_handle.fileno())
        except BaseException as exc:
            interrupted = exc
        finally:
            if partial_stdout.exists():
                os.replace(partial_stdout, stdout)
            if partial_stderr.exists():
                os.replace(partial_stderr, stderr)
        returncode = completed.returncode if completed is not None else None
        validation_error: str | None = None
        payload: dict[str, Any] | None = None
        if interrupted is not None:
            validation_error = f"runner interrupted: {type(interrupted).__name__}: {interrupted}"
        elif returncode == 0:
            try:
                payload = json.loads(partial_json.read_text())
                if not isinstance(payload, dict) or "authority" not in payload:
                    raise ValueError("receipt is missing the required authority object")
            except (OSError, json.JSONDecodeError, ValueError) as exc:
                validation_error = str(exc)
        else:
            validation_error = f"audit exited with status {returncode}"
        promoted = validation_error is None and payload is not None
        if promoted:
            os.replace(partial_json, output_json)
        elif partial_json.exists():
            partial_json.unlink()
        checksum = sha256(output_json) if promoted else None
        if promoted:
            atomic_text(checksum_path, f"{checksum}  {output_json}\n")
        status_payload = execution_status(
            identity, args.stage, command, output_json, stdout, stderr, checksum_path,
            "promoted" if promoted else "failed", returncode, validation_error, checksum,
        )
        atomic_text(status, json.dumps(status_payload, indent=2, sort_keys=True) + "\n")
        row: dict[str, Any] = {
            "id": identity,
            "stage": args.stage,
            "returncode": returncode,
            "output_json": str(output_json),
            "stdout": str(stdout),
            "stderr": str(stderr),
            "status": str(status),
            "receipt_promoted": promoted,
        }
        if promoted and payload is not None:
            evolution = payload.get("finite_galerkin_evolution")
            row["chi_signed"] = payload["static_packet_metrics"]["chi_signed"]
            if evolution is not None:
                row["frozen_packet_recurrence_ratio"] = evolution["frozen_initial_packet_recurrence_ratio"]
                row["moving_packet_recurrence_ratio"] = evolution["moving_packet_recurrence_ratio"]
                row["frozen_integrated_nonlinear_input"] = evolution["integrated_frozen_initial_packet_nonlinear_input"]
        if validation_error is not None:
            row["validation_error"] = validation_error
        rows.append(row)
    summary = {
        "contract": "sequential_local_perturbation_stage_receipt_nonpromoting",
        "authority": {"empirical_non_promoting": True, "theorem_authority": False, "clay_authority": False},
        "manifest": str(args.manifest),
        "stage": args.stage,
        "requested_ids": requested,
        "successful": sum(bool(row["receipt_promoted"]) for row in rows),
        "failed": sum(not bool(row["receipt_promoted"]) for row in rows),
        "rows": rows,
    }
    summary_path = args.output_dir / f"summary_{args.stage}.json"
    summary_path.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
    print(json.dumps(summary, indent=2, sort_keys=True))
    if summary["failed"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
