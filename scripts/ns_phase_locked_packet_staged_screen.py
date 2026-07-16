#!/usr/bin/env python3
"""Plan a bounded, reproducible NS cyclic-packet endpoint screen.

This script deliberately *does not* launch a large CFD batch.  It turns the
allocation-aware 64-case static helicity audit into an immutable manifest of
quarter-window endpoint tasks.  Each task pins one role allocation, one ranked
pure-helicity seed, and one deterministic phase-stream index for
``ns_phase_locked_packet_search.py``.

The manifest is an empirical adversarial-search plan only.  It cannot certify
packet nonrecurrence, a Navier--Stokes estimate, or a Clay claim.
"""

from __future__ import annotations

import argparse
import json
import math
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any


SCRIPT_NAME = "scripts/ns_phase_locked_packet_staged_screen.py"
SEARCH_SCRIPT = Path("scripts/ns_phase_locked_packet_search.py")
DEFAULT_OUTPUT = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_phase_locked_packet_staged_screen_N32_20260716.json"
)

DEFAULT_ALLOCATIONS: tuple[tuple[str, tuple[float, float, float, float]], ...] = (
    ("balanced", (0.30, 0.25, 0.25, 0.20)),
    ("donor-heavy", (0.25, 0.40, 0.15, 0.20)),
    ("feedback-heavy", (0.25, 0.20, 0.15, 0.40)),
    ("target-heavy", (0.50, 0.20, 0.15, 0.15)),
    ("outlet-suppressed", (0.35, 0.30, 0.05, 0.30)),
    ("outlet-enabled", (0.25, 0.20, 0.35, 0.20)),
)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--search-script", type=Path, default=SEARCH_SCRIPT)
    parser.add_argument("--output-json", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--run-directory", type=Path, default=None,
                        help="directory named in task output paths; defaults beside --output-json")
    parser.add_argument("--python", default=sys.executable)
    parser.add_argument("--n", type=int, default=32)
    parser.add_argument("--nu", type=float, default=1.0e-3)
    parser.add_argument("--dt", type=float, default=1.0e-3)
    parser.add_argument("--target-shell", type=int, default=2)
    parser.add_argument("--critical-mass", type=float, default=1.0)
    parser.add_argument("--moving-packet-radius", type=int, default=1)
    parser.add_argument("--phase-samples", type=int, default=8,
                        help="deterministic phase-stream indices 0..phase-samples-1 per static seed")
    parser.add_argument("--backbone-count", type=int, default=8,
                        help="allocation-specific static-helicity seeds retained per role allocation")
    parser.add_argument("--static-pool", type=int, default=32,
                        help="top static envelope ranks from which sign-diverse seeds are chosen")
    parser.add_argument("--quarter-window-c", type=float, default=0.25)
    parser.add_argument("--backend", choices=("cpu", "gpu"), default="gpu",
                        help="backend written into planned commands; the planner never executes it")
    parser.add_argument("--fft-backend", default="vkfft-vulkan")
    parser.add_argument("--save-every", type=int, default=250)
    parser.add_argument("--seed", type=int, default=20260716)
    parser.add_argument("--target-dominance-min", type=float, default=0.10)
    parser.add_argument("--local-tightness-min", type=float, default=0.20)
    parser.add_argument("--role-share-min", type=float, default=0.05)
    return parser.parse_args()


def authority() -> dict[str, bool]:
    return {
        "candidate_only": True,
        "empirical_non_promoting": True,
        "theorem_authority": False,
        "clay_authority": False,
        "promoted": False,
    }


def allocation_argument(shares: tuple[float, float, float, float]) -> str:
    return ",".join(f"{share:.12g}" for share in shares)


def audit_command(
    args: argparse.Namespace, shares: tuple[float, float, float, float], output_path: Path,
) -> list[str]:
    return [
        args.python, str(args.search_script),
        "--backend", "none",
        "--n", str(args.n),
        "--nu", str(args.nu),
        "--dt", str(args.dt),
        "--target-shell", str(args.target_shell),
        "--normalization", "critical",
        "--critical-mass", str(args.critical_mass),
        "--role-shares", allocation_argument(shares),
        "--helicity-static-audit",
        "--phase-samples", "1",
        "--output-json", str(output_path),
    ]


def run_static_audit(args: argparse.Namespace, shares: tuple[float, float, float, float]) -> dict[str, Any]:
    with tempfile.TemporaryDirectory(prefix="ns-phase-static-audit.") as temporary:
        output_path = Path(temporary) / "audit.json"
        subprocess.run(
            audit_command(args, shares, output_path), check=True, capture_output=True, text=True,
        )
        return json.loads(output_path.read_text(encoding="utf-8"))


def feasible_phase_indices(
    args: argparse.Namespace,
    shares: tuple[float, float, float, float],
    backbone_rank: int,
) -> list[int]:
    """Return phase streams that satisfy the exact scheduled task contract.

    The static helicity audit ranks coefficient envelopes, whereas endpoint
    tasks also require packet dominance, local tightness, and each role-share
    floor.  Re-running the cheap ``backend=none`` surface with the *same*
    rank, phase streams, and thresholds prevents the manifest from emitting a
    command that the search script will reject before any CFD evolution.
    """
    with tempfile.TemporaryDirectory(prefix="ns-phase-task-feasibility.") as temporary:
        output_path = Path(temporary) / "feasibility.json"
        command = task_command(
            args, "feasibility", shares, backbone_rank, 0, output_path,
        )
        # ``task_command`` places the backend value immediately after the
        # option; locating the option is robust even when another argument
        # happens to equal the backend's textual value.
        backend_index = command.index("--backend") + 1
        command[backend_index] = "none"
        completed = subprocess.run(command, capture_output=True, text=True)
        if completed.returncode != 0:
            if "no phase samples satisfy the declared" in completed.stderr:
                return []
            raise RuntimeError(
                "exact task-feasibility audit failed unexpectedly:\n"
                f"{completed.stderr.strip()}"
            )
        payload = json.loads(output_path.read_text(encoding="utf-8"))
        return [int(row["sample"]) for row in payload["static_candidates_ranked"]]


def parse_signs(row: dict[str, Any]) -> tuple[int, ...]:
    signs = row["backbone_signs"]
    return tuple(int(signs[key]) for key in sorted(signs))


def hamming(left: tuple[int, ...], right: tuple[int, ...]) -> int:
    return sum(a != b for a, b in zip(left, right, strict=True))


def choose_sign_diverse_ranks(cases: list[dict[str, Any]], pool_size: int, count: int) -> list[int]:
    """Greedily retain high-envelope cases with separated backbone signs.

    The score is deliberately static and modest: it preserves sign diversity
    among a high-envelope pool, but never claims to predict endpoint survival.
    """
    pool = list(enumerate(cases[:min(pool_size, len(cases))]))
    if not pool or count <= 0:
        return []
    selected = [pool[0]]
    remaining = pool[1:]
    while remaining and len(selected) < min(count, len(pool)):
        selected_signs = [parse_signs(row) for _, row in selected]
        # Prefer maximum distance from the selected set.  Envelope rank is the
        # deterministic tie-break, since ``remaining`` retains audit order.
        best_index = max(
            range(len(remaining)),
            key=lambda index: min(hamming(parse_signs(remaining[index][1]), sign) for sign in selected_signs),
        )
        selected.append(remaining.pop(best_index))
    return sorted(rank for rank, _ in selected)


def task_command(
    args: argparse.Namespace,
    allocation_name: str,
    shares: tuple[float, float, float, float],
    backbone_rank: int,
    phase_index: int,
    output_path: Path,
) -> list[str]:
    return [
        args.python, str(args.search_script),
        "--backend", args.backend,
        "--fft-backend", args.fft_backend,
        "--n", str(args.n),
        "--nu", str(args.nu),
        "--dt", str(args.dt),
        "--target-shell", str(args.target_shell),
        "--window-c", str(args.quarter_window_c),
        "--windows", "1",
        "--normalization", "critical",
        "--critical-mass", str(args.critical_mass),
        "--role-shares", allocation_argument(shares),
        "--target-dominance-min", str(args.target_dominance_min),
        "--local-tightness-min", str(args.local_tightness_min),
        "--role-share-min", str(args.role_share_min),
        "--moving-packet-radius", str(args.moving_packet_radius),
        "--helicity-static-case", str(backbone_rank),
        "--phase-samples", str(args.phase_samples),
        "--phase-sample-index", str(phase_index),
        "--seed", str(args.seed),
        "--top-candidates", "1",
        "--save-every", str(args.save_every),
        "--output-json", str(output_path),
    ]


def main() -> None:
    args = parse_args()
    if args.n != 32 or args.target_shell != 2:
        raise ValueError("the current staged plan is calibrated only for N32 target shell j=2")
    if (args.nu <= 0.0 or args.dt <= 0.0 or args.critical_mass <= 0.0
            or args.phase_samples <= 0 or args.backbone_count <= 0 or args.static_pool <= 0):
        raise ValueError("positive numerical and screen-size inputs are required")
    if not args.search_script.is_file():
        raise FileNotFoundError(f"missing search script: {args.search_script}")
    if args.quarter_window_c <= 0.0 or args.quarter_window_c > 1.0:
        raise ValueError("quarter-window-c must lie in (0, 1]")

    run_directory = args.run_directory or args.output_json.parent / "ns_phase_locked_packet_staged_screen_tasks"
    allocation_rows: list[dict[str, Any]] = []
    tasks: list[dict[str, Any]] = []
    for allocation_name, shares in DEFAULT_ALLOCATIONS:
        audit_payload = run_static_audit(args, shares)
        audit = audit_payload["topology"]["helicity_static_factor_audit"]
        cases = audit["cases_ranked_by_independently_maximized_envelope_sum"]
        candidate_ranks = choose_sign_diverse_ranks(cases, args.static_pool, args.backbone_count)
        feasible_by_rank = {
            rank: feasible_phase_indices(args, shares, rank)
            for rank in candidate_ranks
        }
        ranks = [rank for rank in candidate_ranks if feasible_by_rank[rank]]
        allocation_rows.append({
            "name": allocation_name,
            "role_shares": dict(zip(("target", "donor", "outlet", "feedback"), shares, strict=True)),
            "static_audit_contract": audit["warning"],
            "selected_backbone_ranks": ranks,
            "skipped_infeasible_backbone_ranks": [
                rank for rank in candidate_ranks if not feasible_by_rank[rank]
            ],
            "selected_backbone_cases": [
                {
                    "rank": rank,
                    "backbone_signs": cases[rank]["backbone_signs"],
                    "independently_maximized_envelope_sum": cases[rank]["independently_maximized_envelope_sum"],
                }
                for rank in ranks
            ],
        })
        for rank in ranks:
            for phase_index in feasible_by_rank[rank]:
                filename = f"quarter_{allocation_name}_rank{rank:02d}_phase{phase_index:03d}.json"
                output_path = run_directory / filename
                command = task_command(args, allocation_name, shares, rank, phase_index, output_path)
                tasks.append({
                    "stage": "quarter-window",
                    "allocation": allocation_name,
                    "role_shares": dict(zip(("target", "donor", "outlet", "feedback"), shares, strict=True)),
                    "helicity_static_rank": rank,
                    "phase_sample_index": phase_index,
                    "output_json": str(output_path),
                    "command": command,
                    "shell_command": " ".join(__import__("shlex").quote(part) for part in command),
                })

    nominal_time = args.quarter_window_c * 2.0 ** (-2 * args.target_shell) / args.nu
    payload = {
        "contract": "ns_phase_locked_packet_staged_screen_plan",
        "authority": authority(),
        "status": "planned_not_executed",
        "scope": (
            "allocation-aware static pure-helicity seeds followed by single exact phase-stream "
            "quarter-window endpoint tasks; no global optimisation, recurrence theorem, or NS estimate"
        ),
        "selection_rule": {
            "static_pool": args.static_pool,
            "backbone_count": args.backbone_count,
            "rule": "rank-0 envelope seed plus greedy maximum Hamming separation inside the allocation-specific top static pool",
            "warning": "static sign diversity is a scheduling heuristic, not a physical equivalence or endpoint predictor",
        },
        "quarter_window": {
            "window_c": args.quarter_window_c,
            "nominal_time": nominal_time,
            "endpoint_metric": "moving_packet_recurrence_ratio is primary; designed role ledger and target capture are explanatory telemetry",
        },
        "allocation_families": allocation_rows,
        "task_count": len(tasks),
        "tasks": tasks,
        "next_selection_protocol": [
            "Run only a bounded subset of quarter-window tasks, respecting available CPU/GPU capacity.",
            "Rank endpoint files by moving-packet survival while preserving allocation and helicity diversity.",
            "Use gross designed-loop throughput and full-target capture as diagnostics, not a replacement score.",
            "Promote only selected survivors to half/full windows after inspecting the generated results.",
        ],
        "decision": "candidate-only experimental task plan; execution is intentionally external and explicit",
    }
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(json.dumps(payload, indent=2, sort_keys=True, allow_nan=False) + "\n", encoding="utf-8")
    print(json.dumps(payload, indent=2, sort_keys=True, allow_nan=False))


if __name__ == "__main__":
    main()
