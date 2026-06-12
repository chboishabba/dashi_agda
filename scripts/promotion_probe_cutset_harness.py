#!/usr/bin/env python3
"""Summarize promotion-probe runner output into a canonical JSON artifact."""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from pathlib import Path

DEFAULT_LOG_ROOT = Path("logs/agda-promotion-probe-cutset")
DEFAULT_OUTPUT = Path("outputs/promotion_probe_cutset_summary.json")


@dataclass(frozen=True)
class TargetSummary:
    target: str
    status: str
    log_file: str


@dataclass(frozen=True)
class Result:
    everything_target: str
    everything_status: str
    ns_probe_status: str
    ym_probe_status: str
    unification_probe_status: str
    profile_probe_status: str
    probe_failures_expected: bool
    aggregate_green_and_probe_red: bool
    target_count: int
    summaries: list[TargetSummary]


def parse_summary_line(line: str) -> TargetSummary | None:
    parts = line.rstrip("\n").split("\t")
    if len(parts) != 3:
      return None
    status, target, log_file = parts
    return TargetSummary(target=target, status=status, log_file=log_file)


def latest_run_dir(log_root: Path) -> Path:
    candidates = [path for path in log_root.iterdir() if path.is_dir()]
    if not candidates:
        raise FileNotFoundError(f"no run directories under {log_root}")
    return max(candidates, key=lambda path: path.name)


def load_summaries(run_dir: Path) -> list[TargetSummary]:
    summary_file = run_dir / "summary.tsv"
    if not summary_file.exists():
        raise FileNotFoundError(f"missing summary file: {summary_file}")
    rows: list[TargetSummary] = []
    for line in summary_file.read_text(encoding="utf-8").splitlines():
        row = parse_summary_line(line)
        if row is not None:
            rows.append(row)
    if not rows:
        raise ValueError(f"no target rows found in {summary_file}")
    return rows


def lookup(rows: list[TargetSummary], target: str) -> str:
    for row in rows:
        if row.target == target:
            return row.status
    raise KeyError(f"target not found in summary: {target}")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--log-root", type=Path, default=DEFAULT_LOG_ROOT)
    parser.add_argument("--run-dir", type=Path)
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--json-output", type=Path, default=DEFAULT_OUTPUT)
    args = parser.parse_args()

    run_dir = args.run_dir or latest_run_dir(args.log_root)
    rows = load_summaries(run_dir)

    everything_target = "DASHI/Everything.agda"
    ns_target = "DASHI/Physics/Probes/NSPromotionProbe.agda"
    ym_target = "DASHI/Physics/Probes/YMPromotionProbe.agda"
    unification_target = "DASHI/Physics/Probes/UnificationPromotionProbe.agda"
    profile_target = "DASHI/Physics/Probes/CurrentProofProfilePromotionProbe.agda"

    everything_status = lookup(rows, everything_target)
    ns_status = lookup(rows, ns_target)
    ym_status = lookup(rows, ym_target)
    unification_status = lookup(rows, unification_target)
    profile_status = lookup(rows, profile_target)

    probe_failures_expected = all(
        status == "FAIL"
        for status in [ns_status, ym_status, unification_status, profile_status]
    )
    aggregate_green_and_probe_red = (
        everything_status == "PASS" and probe_failures_expected
    )

    result = Result(
        everything_target=everything_target,
        everything_status=everything_status,
        ns_probe_status=ns_status,
        ym_probe_status=ym_status,
        unification_probe_status=unification_status,
        profile_probe_status=profile_status,
        probe_failures_expected=probe_failures_expected,
        aggregate_green_and_probe_red=aggregate_green_and_probe_red,
        target_count=len(rows),
        summaries=rows,
    )

    args.json_output.parent.mkdir(parents=True, exist_ok=True)
    args.json_output.write_text(
        json.dumps(asdict(result), indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )

    if args.json:
        print(json.dumps(asdict(result), indent=2, sort_keys=True))
    else:
        print(f"aggregate_green_and_probe_red={result.aggregate_green_and_probe_red}")
        print(f"probe_failures_expected={result.probe_failures_expected}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
