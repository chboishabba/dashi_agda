#!/usr/bin/env python3
"""Run a selected stage of the local NS perturbation manifest sequentially.

This runner intentionally executes one finite-Galerkin candidate at a time.
It is a bounded empirical scheduler, not an optimiser and not theorem
authority.  The manifest's explicit stages provide the only promotion path:
static -> .05T -> .10T -> .25T.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import subprocess
import sys
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
        command = [args.python, str(args.audit_script), *stage_arguments(entry, args.stage), "--output-json", str(output_json)]
        print(f"[{ordinal}/{len(requested)}] {identity} stage={args.stage}", flush=True)
        completed = subprocess.run(command, text=True, capture_output=True)
        stdout.write_text(completed.stdout)
        stderr.write_text(completed.stderr)
        row: dict[str, Any] = {
            "id": identity,
            "stage": args.stage,
            "returncode": completed.returncode,
            "output_json": str(output_json),
            "stdout": str(stdout),
            "stderr": str(stderr),
        }
        if completed.returncode == 0 and output_json.is_file():
            payload = json.loads(output_json.read_text())
            evolution = payload.get("finite_galerkin_evolution")
            row["chi_signed"] = payload["static_packet_metrics"]["chi_signed"]
            if evolution is not None:
                row["frozen_packet_recurrence_ratio"] = evolution["frozen_initial_packet_recurrence_ratio"]
                row["moving_packet_recurrence_ratio"] = evolution["moving_packet_recurrence_ratio"]
                row["frozen_integrated_nonlinear_input"] = evolution["integrated_frozen_initial_packet_nonlinear_input"]
        rows.append(row)
    summary = {
        "contract": "sequential_local_perturbation_stage_receipt_nonpromoting",
        "authority": {"empirical_non_promoting": True, "theorem_authority": False, "clay_authority": False},
        "manifest": str(args.manifest),
        "stage": args.stage,
        "requested_ids": requested,
        "successful": sum(row["returncode"] == 0 for row in rows),
        "failed": sum(row["returncode"] != 0 for row in rows),
        "rows": rows,
    }
    summary_path = args.output_dir / f"summary_{args.stage}.json"
    summary_path.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
    print(json.dumps(summary, indent=2, sort_keys=True))
    if summary["failed"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
