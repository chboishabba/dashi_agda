#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import subprocess
import sys
import time
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Sequence

ROOT = Path(__file__).resolve().parents[1]
QUEUE_SCRIPT = ROOT / "scripts" / "generate_layer2_long_compute_queue.py"

L0_TARGETS = [
    "Ontology/Hecke/Layer2FiniteSearchShell.agda",
    "Kernel/Monoid.agda",
    "Verification/Prelude.agda",
    "DASHI/Physics/Closure/CanonicalPrimeSelectionBridge.agda",
    "DASHI/Physics/Closure/CanonicalPrimeInvariance.agda",
    "DASHI/Physics/Closure/CanonicalPrimeConcentration.agda",
    "DASHI/Physics/Closure/CanonicalPrimeSelector.agda",
    "DASHI/Physics/Closure/CanonicalPrimeIsolation.agda",
]

L1_TARGETS = [
    "Ontology/Hecke/SaturatedInvariantRefinementStatus.agda",
]


@dataclass(frozen=True)
class Step:
    name: str
    kind: str
    command: list[str]
    expected_lane: str


@dataclass
class StepResult:
    name: str
    kind: str
    expected_lane: str
    command: list[str]
    status: str
    duration_s: float
    returncode: int | None


def agda_step(target: str) -> Step:
    return Step(
        name=target,
        kind="agda",
        command=["agda", "-i", ".", target],
        expected_lane="L0",
    )


def bounded_agda_step(target: str, timeout_s: int) -> Step:
    return Step(
        name=target,
        kind="agda",
        command=["timeout", str(timeout_s), "agda", "-i", ".", target],
        expected_lane="L1",
    )


def queue_step(queue_dir: Path, jobs: int) -> Step:
    return Step(
        name="Layer2QueueGeneration",
        kind="queue",
        command=[
            sys.executable,
            str(QUEUE_SCRIPT),
            "--include-commands",
            "--parallel",
            "-j",
            str(jobs),
            "--write-batch-files",
            str(queue_dir),
        ],
        expected_lane="L2-control",
    )


def build_steps(include_medium: bool, include_queue: bool, timeout_s: int, queue_dir: Path, jobs: int) -> list[Step]:
    steps = [agda_step(target) for target in L0_TARGETS]
    if include_medium:
        steps.extend(bounded_agda_step(target, timeout_s) for target in L1_TARGETS)
    if include_queue:
        steps.append(queue_step(queue_dir, jobs))
    return steps


def run_step(step: Step, cwd: Path) -> StepResult:
    started = time.monotonic()
    try:
        proc = subprocess.run(step.command, cwd=cwd, check=False)
    except OSError:
        return StepResult(
            name=step.name,
            kind=step.kind,
            expected_lane=step.expected_lane,
            command=step.command,
            status="error",
            duration_s=time.monotonic() - started,
            returncode=None,
        )
    duration = time.monotonic() - started
    status = "ok" if proc.returncode == 0 else "failed"
    if step.command and step.command[0] == "timeout" and proc.returncode == 124:
        status = "timed_out"
    return StepResult(
        name=step.name,
        kind=step.kind,
        expected_lane=step.expected_lane,
        command=step.command,
        status=status,
        duration_s=duration,
        returncode=proc.returncode,
    )


def render_plan(steps: Sequence[Step]) -> str:
    lines = []
    for idx, step in enumerate(steps, start=1):
        lines.append(f"{idx}. [{step.expected_lane}] {step.name}")
        lines.append(f"   {' '.join(step.command)}")
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Run the current easy->hard Agda validation order: thin validated targets first, "
            "optional bounded medium target next, and optional Layer 2 queue generation last."
        )
    )
    parser.add_argument("--include-medium", action="store_true", help="Append bounded L1 targets after the easy L0 run.")
    parser.add_argument("--include-queue", action="store_true", help="Finish by generating the offline Layer 2 queue instead of attempting heavy Agda execution.")
    parser.add_argument("--timeout", type=int, default=90, help="Timeout in seconds for bounded L1 targets. Default: 90.")
    parser.add_argument("--queue-dir", default="/tmp/layer2-queue", help="Output directory for --include-queue. Default: /tmp/layer2-queue.")
    parser.add_argument("--jobs", type=int, default=4, help="Parallelism hint forwarded to queue generation. Default: 4.")
    parser.add_argument("--format", choices=("text", "json"), default="text", help="Output format. Default: text.")
    parser.add_argument("--dry-run", action="store_true", help="Print the ordered plan without executing it.")
    parser.add_argument("--keep-going", action="store_true", help="Continue after a failed/timed-out step instead of stopping.")
    args = parser.parse_args()

    steps = build_steps(
        include_medium=args.include_medium,
        include_queue=args.include_queue,
        timeout_s=args.timeout,
        queue_dir=Path(args.queue_dir),
        jobs=args.jobs,
    )

    if args.dry_run:
        if args.format == "json":
            payload = {
                "mode": "dry-run",
                "steps": [asdict(step) for step in steps],
            }
            print(json.dumps(payload, indent=2))
        else:
            print(render_plan(steps))
        return 0

    results: list[StepResult] = []
    for step in steps:
        result = run_step(step, ROOT)
        results.append(result)
        if result.status != "ok" and not args.keep_going:
            break

    if args.format == "json":
        payload = {
            "mode": "executed",
            "root": str(ROOT),
            "results": [asdict(result) for result in results],
        }
        print(json.dumps(payload, indent=2))
    else:
        for result in results:
            print(
                f"[{result.status}] {result.name} ({result.expected_lane}) "
                f"{result.duration_s:.2f}s"
            )
            print(f"  {' '.join(result.command)}")
    return 0 if all(r.status == "ok" for r in results) else 1


if __name__ == "__main__":
    raise SystemExit(main())
