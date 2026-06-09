#!/usr/bin/env python3
"""Sprint 123 phase-locking dwell-window sampler."""

from __future__ import annotations

import argparse
import csv
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint123_phase_locking_dwell_sampler"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint123_phase_locking_dwell_sampler")
SUMMARY_NAME = "ns_sprint123_phase_locking_dwell_sampler_summary.json"
ROWS_NAME = "ns_sprint123_phase_locking_dwell_sampler_rows.json"
CSV_NAME = "ns_sprint123_phase_locking_dwell_sampler_rows.csv"
REPORT_NAME = "ns_sprint123_phase_locking_dwell_sampler.md"

ROTATION_RATE_VALUES = (0.25, 0.5, 1.0, 1.5, 2.0)
DRIFT_RATE_VALUES = (0.0, 0.125, 0.25, 0.5, 1.0)
DAMPING_RATE_VALUES = (0.0, 0.05, 0.1, 0.2)
INITIAL_PHASE_VALUES = (0.0, math.pi / 32.0, math.pi / 16.0, math.pi / 8.0, math.pi / 4.0)
DURATION_VALUES = (1.0, 2.0, 4.0, 8.0)
TOLERANCE = 1.0e-12


@dataclass(frozen=True)
class PhaseLockingDwellRow:
    row_id: str
    rotation_rate: float
    drift_rate: float
    damping_rate: float
    initial_phase: float
    duration: float
    theta_formula: str
    amplitude_weight_formula: str
    effective_phase_rate: float
    favorable_rule: str
    favorable_interval_count: int
    positive_dwell_time: float
    weighted_dwell: float
    max_contiguous_favorable_window: float
    favorable_dwell: bool
    classification: str

    def as_row(self) -> dict[str, Any]:
        return asdict(self)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--out-dir", type=Path, default=OUT_DIR_DEFAULT)
    return parser.parse_args()


def clean(value: float) -> float:
    if abs(value) < TOLERANCE:
        return 0.0
    return value


def theta_at(initial_phase: float, effective_phase_rate: float, t: float) -> float:
    return initial_phase + effective_phase_rate * t


def is_favorable(theta: float) -> bool:
    doubled = 2.0 * theta
    return math.cos(doubled) > TOLERANCE and math.sin(doubled) > TOLERANCE


def weighted_interval(start: float, stop: float, damping_rate: float) -> float:
    if stop <= start:
        return 0.0
    if abs(damping_rate) < TOLERANCE:
        return stop - start
    return (math.exp(-damping_rate * start) - math.exp(-damping_rate * stop)) / damping_rate


def merge_intervals(intervals: list[tuple[float, float]]) -> list[tuple[float, float]]:
    if not intervals:
        return []
    ordered = sorted(intervals)
    merged = [ordered[0]]
    for start, stop in ordered[1:]:
        old_start, old_stop = merged[-1]
        if start <= old_stop + TOLERANCE:
            merged[-1] = (old_start, max(old_stop, stop))
        else:
            merged.append((start, stop))
    return merged


def favorable_intervals(
    initial_phase: float,
    effective_phase_rate: float,
    duration: float,
) -> list[tuple[float, float]]:
    if duration <= 0.0:
        return []
    if abs(effective_phase_rate) < TOLERANCE:
        return [(0.0, duration)] if is_favorable(initial_phase) else []

    theta_start = theta_at(initial_phase, effective_phase_rate, 0.0)
    theta_stop = theta_at(initial_phase, effective_phase_rate, duration)
    theta_min = min(theta_start, theta_stop)
    theta_max = max(theta_start, theta_stop)

    k_min = math.floor((theta_min - math.pi / 4.0) / math.pi) - 1
    k_max = math.ceil(theta_max / math.pi) + 1
    intervals: list[tuple[float, float]] = []

    for k in range(k_min, k_max + 1):
        lower_theta = k * math.pi
        upper_theta = lower_theta + math.pi / 4.0
        t_a = (lower_theta - initial_phase) / effective_phase_rate
        t_b = (upper_theta - initial_phase) / effective_phase_rate
        start = max(0.0, min(t_a, t_b))
        stop = min(duration, max(t_a, t_b))
        if stop - start > TOLERANCE:
            intervals.append((clean(start), clean(stop)))

    return merge_intervals(intervals)


def classify(positive_dwell_time: float, duration: float) -> str:
    if positive_dwell_time <= TOLERANCE:
        return "no_favorable_dwell"
    if positive_dwell_time >= duration - TOLERANCE:
        return "full_favorable_dwell"
    return "partial_favorable_dwell"


def build_rows() -> list[PhaseLockingDwellRow]:
    rows: list[PhaseLockingDwellRow] = []
    for rotation_rate in ROTATION_RATE_VALUES:
        for drift_rate in DRIFT_RATE_VALUES:
            for damping_rate in DAMPING_RATE_VALUES:
                for initial_phase in INITIAL_PHASE_VALUES:
                    for duration in DURATION_VALUES:
                        effective_phase_rate = rotation_rate - drift_rate
                        intervals = favorable_intervals(
                            initial_phase=initial_phase,
                            effective_phase_rate=effective_phase_rate,
                            duration=duration,
                        )
                        positive_dwell_time = sum(stop - start for start, stop in intervals)
                        weighted_dwell = sum(
                            weighted_interval(start, stop, damping_rate)
                            for start, stop in intervals
                        )
                        max_window = max((stop - start for start, stop in intervals), default=0.0)
                        rows.append(
                            PhaseLockingDwellRow(
                                row_id=f"r{len(rows):04d}",
                                rotation_rate=rotation_rate,
                                drift_rate=drift_rate,
                                damping_rate=damping_rate,
                                initial_phase=initial_phase,
                                duration=duration,
                                theta_formula="theta(t)=theta0+(rotation_rate-drift_rate)*t",
                                amplitude_weight_formula="exp(-damping_rate*t)",
                                effective_phase_rate=effective_phase_rate,
                                favorable_rule="cos(2*theta)>0 and sin(2*theta)>0",
                                favorable_interval_count=len(intervals),
                                positive_dwell_time=clean(positive_dwell_time),
                                weighted_dwell=clean(weighted_dwell),
                                max_contiguous_favorable_window=clean(max_window),
                                favorable_dwell=positive_dwell_time > TOLERANCE,
                                classification=classify(positive_dwell_time, duration),
                            )
                        )
    return rows


def write_json(path: Path, payload: Any) -> None:
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def write_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    if not rows:
        raise ValueError("cannot write empty row set")
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)


def format_value(value: Any) -> str:
    if isinstance(value, bool):
        return str(value).lower()
    if isinstance(value, float):
        return f"{value:.12g}"
    return str(value)


def build_summary(rows: list[dict[str, Any]]) -> dict[str, Any]:
    favorable_rows = [row for row in rows if row["favorable_dwell"]]
    positive_dwell_times = [float(row["positive_dwell_time"]) for row in rows]
    weighted_dwells = [float(row["weighted_dwell"]) for row in rows]
    max_windows = [float(row["max_contiguous_favorable_window"]) for row in rows]
    return {
        "contract": CONTRACT,
        "row_count": len(rows),
        "rotation_rate_values": list(ROTATION_RATE_VALUES),
        "drift_rate_values": list(DRIFT_RATE_VALUES),
        "damping_rate_values": list(DAMPING_RATE_VALUES),
        "initial_phase_values": list(INITIAL_PHASE_VALUES),
        "duration_values": list(DURATION_VALUES),
        "theta_formula": "theta(t)=theta0+(rotation_rate-drift_rate)*t",
        "amplitude_weight_formula": "exp(-damping_rate*t)",
        "favorable_rule": "cos(2*theta)>0 and sin(2*theta)>0",
        "favorable_dwell_rows_count": len(favorable_rows),
        "positive_dwell_time_min": min(positive_dwell_times),
        "positive_dwell_time_max": max(positive_dwell_times),
        "weighted_dwell_min": min(weighted_dwells),
        "weighted_dwell_max": max(weighted_dwells),
        "max_contiguous_favorable_window_min": min(max_windows),
        "max_contiguous_favorable_window_max": max(max_windows),
        "nse_derived_phase_locking_established": False,
        "favorable_window_lower_bound_closed": False,
        "clay": False,
        "complete": True,
        "exit_code": 0,
    }


def markdown_table(rows: list[dict[str, Any]]) -> str:
    headers = (
        "row",
        "rotation",
        "drift",
        "damping",
        "theta0",
        "duration",
        "dwell",
        "weighted",
        "max window",
        "class",
    )
    keys = (
        "row_id",
        "rotation_rate",
        "drift_rate",
        "damping_rate",
        "initial_phase",
        "duration",
        "positive_dwell_time",
        "weighted_dwell",
        "max_contiguous_favorable_window",
        "classification",
    )
    lines = [
        "| " + " | ".join(headers) + " |",
        "| " + " | ".join("---" for _ in headers) + " |",
    ]
    for row in rows:
        lines.append("| " + " | ".join(format_value(row[key]) for key in keys) + " |")
    return "\n".join(lines)


def write_report(path: Path, summary: dict[str, Any], rows: list[dict[str, Any]]) -> None:
    text = "\n".join(
        (
            f"# {CONTRACT}",
            "",
            "Deterministic sampler for phase-locking dwell windows.",
            "",
            "Formula surface:",
            "",
            "- theta(t)=theta0+(rotation_rate-drift_rate)*t",
            "- amplitude weight = exp(-damping_rate*t)",
            "- favorable iff cos(2*theta)>0 and sin(2*theta)>0",
            "- positive_dwell_time is total favorable interval length",
            "- weighted_dwell integrates amplitude weight over favorable intervals",
            "- max_contiguous_favorable_window is the longest favorable interval",
            "",
            "Summary:",
            "",
            "- favorable_dwell_rows_count: "
            f"{format_value(summary['favorable_dwell_rows_count'])}",
            "- nse_derived_phase_locking_established: "
            f"{format_value(summary['nse_derived_phase_locking_established'])}",
            "- favorable_window_lower_bound_closed: "
            f"{format_value(summary['favorable_window_lower_bound_closed'])}",
            f"- clay: {format_value(summary['clay'])}",
            "",
            markdown_table(rows),
            "",
        )
    )
    path.write_text(text, encoding="utf-8")


def main() -> int:
    args = parse_args()
    out_dir = args.out_dir
    if not out_dir.is_absolute():
        out_dir = args.repo_root / out_dir
    out_dir.mkdir(parents=True, exist_ok=True)

    rows = [row.as_row() for row in build_rows()]
    summary = build_summary(rows)

    write_json(out_dir / ROWS_NAME, rows)
    write_json(out_dir / SUMMARY_NAME, summary)
    write_csv(out_dir / CSV_NAME, rows)
    write_report(out_dir / REPORT_NAME, summary, rows)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
