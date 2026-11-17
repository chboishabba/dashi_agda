#!/usr/bin/env python3
"""Run Agda 2.9 frontier checks and collect a JSON audit report."""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Iterable


ROOT = Path(__file__).resolve().parents[1]
WRAPPER = ROOT / "scripts" / "run_agda29_parallel_check.sh"
DEFAULT_OUT = ROOT / "artifacts" / "agda29_frontier" / "agda29_frontier_audit.json"
DEFAULT_TARGET = "DASHI/Everything.agda"


SOURCE_LOCATION_RE = re.compile(
    r"(?P<path>(?:[A-Za-z]:)?[^:\n]+?\.agda|(?:[A-Za-z]:)?[^:\n]+?\.lagda(?:\.[A-Za-z]+)?)"
    r":(?P<line>\d+)(?:,(?P<column>\d+)(?:-\d+)?)?"
)


@dataclass(frozen=True)
class BatchResult:
    index: int
    targets: list[str]
    command: list[str]
    returncode: int
    stdout: str
    stderr: str
    started_at: str
    finished_at: str
    duration_seconds: float
    first_failure: dict[str, object] | None

    def to_json(self) -> dict[str, object]:
        return {
            "index": self.index,
            "targets": self.targets,
            "command": self.command,
            "returncode": self.returncode,
            "stdout": self.stdout,
            "stderr": self.stderr,
            "started_at": self.started_at,
            "finished_at": self.finished_at,
            "duration_seconds": self.duration_seconds,
            "first_failure": self.first_failure,
        }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Run scripts/run_agda29_parallel_check.sh over target paths and record a JSON frontier audit."
    )
    parser.add_argument(
        "targets",
        nargs="*",
        default=[DEFAULT_TARGET],
        help="Agda target paths to check. Defaults to DASHI/Everything.agda.",
    )
    parser.add_argument("--jobs", type=int, default=8, help="Jobs passed to AGDA_JOBS for the wrapper.")
    parser.add_argument(
        "--batch-size",
        type=int,
        default=1,
        help="Number of targets per wrapper invocation.",
    )
    parser.add_argument(
        "--out",
        type=Path,
        default=DEFAULT_OUT,
        help="JSON report path. Defaults to artifacts/agda29_frontier/agda29_frontier_audit.json.",
    )
    parser.add_argument(
        "--stop-on-failure",
        action="store_true",
        help="Stop after the first failing batch.",
    )
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("--jobs must be >= 1")
    if args.batch_size < 1:
        parser.error("--batch-size must be >= 1")
    return args


def chunked(items: list[str], size: int) -> Iterable[list[str]]:
    for start in range(0, len(items), size):
        yield items[start : start + size]


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat()


def extract_first_failure(texts: list[str], targets: list[str]) -> dict[str, object] | None:
    for text in texts:
        for line in text.splitlines():
            match = SOURCE_LOCATION_RE.search(line)
            if not match:
                continue
            source_path = match.group("path")
            line_no = int(match.group("line"))
            column = match.group("column")
            normalized_path = source_path
            candidate = Path(source_path)
            if not candidate.is_absolute():
                normalized_path = candidate.as_posix()
            return {
                "path": normalized_path,
                "line": line_no,
                "column": int(column) if column is not None else None,
                "line_text": line.strip(),
                "target_hint": targets[0] if targets else None,
            }
    return None


def run_batch(index: int, targets: list[str], jobs: int) -> BatchResult:
    command = ["bash", str(WRAPPER), *targets]
    started = datetime.now(timezone.utc)
    completed = subprocess.run(
        command,
        cwd=ROOT,
        env={**os.environ, "AGDA_JOBS": str(jobs)},
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
        check=False,
    )
    finished = datetime.now(timezone.utc)
    stdout = completed.stdout or ""
    stderr = completed.stderr or ""
    first_failure = (
        extract_first_failure([stderr, stdout], targets) if completed.returncode != 0 else None
    )
    duration_seconds = (finished - started).total_seconds()
    return BatchResult(
        index=index,
        targets=targets,
        command=command,
        returncode=completed.returncode,
        stdout=stdout,
        stderr=stderr,
        started_at=started.isoformat(),
        finished_at=finished.isoformat(),
        duration_seconds=duration_seconds,
        first_failure=first_failure,
    )


def summarize(batches: list[BatchResult]) -> dict[str, object]:
    total_targets = sum(len(batch.targets) for batch in batches)
    failed_batches = [batch for batch in batches if batch.returncode != 0]
    first_failure = None
    for batch in failed_batches:
        if batch.first_failure is not None:
            first_failure = {
                "batch_index": batch.index,
                "targets": batch.targets,
                **batch.first_failure,
            }
            break
        first_failure = {
            "batch_index": batch.index,
            "targets": batch.targets,
            "path": None,
            "line": None,
            "column": None,
            "line_text": None,
        }
        break

    return {
        "total_targets": total_targets,
        "total_batches": len(batches),
        "succeeded_batches": len(batches) - len(failed_batches),
        "failed_batches": len(failed_batches),
        "failed_targets_upper_bound": sum(len(batch.targets) for batch in failed_batches),
        "first_failure": first_failure,
        "exit_code": 0 if not failed_batches else 1,
    }


def main() -> int:
    args = parse_args()
    targets = [str(target) for target in args.targets]
    batches = list(chunked(targets, args.batch_size))
    started_at = now_iso()
    batch_results: list[BatchResult] = []

    print(
        f"Running {len(targets)} target(s) in {len(batches)} batch(es) with AGDA_JOBS={args.jobs}",
        flush=True,
    )

    for batch_index, batch_targets in enumerate(batches, start=1):
        print(
            f"[{batch_index}/{len(batches)}] checking {len(batch_targets)} target(s): {', '.join(batch_targets)}",
            flush=True,
        )
        result = run_batch(batch_index, batch_targets, args.jobs)
        batch_results.append(result)
        if result.returncode == 0:
            print(f"[{batch_index}/{len(batches)}] ok", flush=True)
        else:
            failure = result.first_failure
            if failure and failure.get("path") and failure.get("line"):
                location = f"{failure['path']}:{failure['line']}"
                if failure.get("column") is not None:
                    location += f":{failure['column']}"
                print(f"[{batch_index}/{len(batches)}] failed at {location}", flush=True)
            else:
                print(f"[{batch_index}/{len(batches)}] failed with exit code {result.returncode}", flush=True)
            if args.stop_on_failure:
                break

    summary = summarize(batch_results)
    finished_at = now_iso()
    report = {
        "tool": "agda29_frontier_audit",
        "repo_root": str(ROOT),
        "wrapper": str(WRAPPER),
        "jobs": args.jobs,
        "batch_size": args.batch_size,
        "stop_on_failure": args.stop_on_failure,
        "targets": targets,
        "started_at": started_at,
        "finished_at": finished_at,
        "batches": [batch.to_json() for batch in batch_results],
        "summary": summary,
    }

    out_path = args.out
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    print(f"Report written to {out_path}", flush=True)
    if summary["first_failure"]:
        failure = summary["first_failure"]
        path = failure.get("path")
        line = failure.get("line")
        column = failure.get("column")
        if path and line:
            location = f"{path}:{line}"
            if column is not None:
                location += f":{column}"
            print(f"First recognizable failure: {location}", flush=True)

    return int(summary["exit_code"])


if __name__ == "__main__":
    raise SystemExit(main())
