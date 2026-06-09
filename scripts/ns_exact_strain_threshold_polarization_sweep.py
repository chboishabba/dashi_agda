#!/usr/bin/env python3
"""Sweep exact-strain NS zero-mode diagnostics over thresholds and polarizations.

This is a local falsification harness only.  It repeatedly invokes
``scripts/ns_triadic_output_width_harness.py`` with ``--frame-model
exact-strain`` and records how the current Family-I/II zero-mode formulation
behaves across:

* tolerance thresholds,
* exact input-polarization models,
* seeds,
* sample counts.

The key output is whether the present Family-I/II formulation is permissive:
large zero-hit fractions and large depth-2 survival under exact strain mean the
finite theorem target needs strengthening before analytic NS leakage transfer
is worth promoting.  This script is diagnostic only and always reports
``promotion=false``.
"""

from __future__ import annotations

import argparse
import itertools
import json
import statistics
import subprocess
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable, Sequence


SCRIPT_DIR = Path(__file__).resolve().parent
DEFAULT_CHILD = SCRIPT_DIR / "ns_triadic_output_width_harness.py"


@dataclass(frozen=True)
class SweepCase:
    tolerance: float
    polarization: str
    seed: int
    samples: int


def parse_csv_floats(value: str) -> list[float]:
    out: list[float] = []
    for chunk in value.split(","):
        chunk = chunk.strip()
        if not chunk:
            continue
        out.append(float(chunk))
    if not out:
        raise argparse.ArgumentTypeError("expected at least one float")
    return out


def parse_csv_ints(value: str) -> list[int]:
    out: list[int] = []
    for chunk in value.split(","):
        chunk = chunk.strip()
        if not chunk:
            continue
        out.append(int(chunk))
    if not out:
        raise argparse.ArgumentTypeError("expected at least one integer")
    return out


def parse_csv_strings(value: str) -> list[str]:
    allowed = {"canonical", "seeded", "helical-plus", "helical-minus"}
    out: list[str] = []
    for chunk in value.split(","):
        chunk = chunk.strip()
        if not chunk:
            continue
        if chunk not in allowed:
            raise argparse.ArgumentTypeError(
                f"unknown polarization {chunk!r}; expected one of {sorted(allowed)}"
            )
        out.append(chunk)
    if not out:
        raise argparse.ArgumentTypeError("expected at least one polarization")
    return out


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--tolerances",
        type=parse_csv_floats,
        default=parse_csv_floats("1e-1,5e-2,1e-2,5e-3,1e-3"),
        help="comma-separated zero-mode residual tolerances",
    )
    parser.add_argument(
        "--polarizations",
        type=parse_csv_strings,
        default=parse_csv_strings("canonical,seeded,helical-plus,helical-minus"),
        help="comma-separated exact-strain input polarization models",
    )
    parser.add_argument(
        "--seeds",
        type=parse_csv_ints,
        default=parse_csv_ints("20260608,7"),
        help="comma-separated sampler seeds",
    )
    parser.add_argument(
        "--sample-counts",
        type=parse_csv_ints,
        default=parse_csv_ints("400"),
        help="comma-separated sample counts",
    )
    parser.add_argument("--normals", type=int, default=256)
    parser.add_argument("--bins", type=int, default=256)
    parser.add_argument("--depth2-trials-per-hit", type=int, default=2)
    parser.add_argument("--axis", nargs=3, type=float, default=(0.0, 0.0, 1.0))
    parser.add_argument(
        "--child-script",
        type=Path,
        default=DEFAULT_CHILD,
        help="path to ns_triadic_output_width_harness.py",
    )
    parser.add_argument(
        "--timeout-seconds",
        type=float,
        default=120.0,
        help="timeout per child harness invocation",
    )
    parser.add_argument(
        "--json-output",
        type=Path,
        default=None,
        help="optional path to write the complete JSON report",
    )
    parser.add_argument(
        "--print-child-commands",
        action="store_true",
        help="include child command arrays in each case result",
    )
    return parser.parse_args(argv)


def mean(values: Iterable[float]) -> float | None:
    xs = list(values)
    if not xs:
        return None
    return sum(xs) / len(xs)


def median(values: Iterable[float]) -> float | None:
    xs = list(values)
    if not xs:
        return None
    return float(statistics.median(xs))


def width_value(summary: dict[str, Any]) -> float | None:
    value = summary.get("estimated_width_zero_outputs")
    if value is None:
        return None
    return float(value)


def depth2_fraction(summary: dict[str, Any]) -> float | None:
    value = summary.get("depth2_hit_fraction_among_single_hits")
    if value is None:
        return None
    return float(value)


def hit_fraction(summary: dict[str, Any]) -> float:
    return float(summary.get("hit_fraction_single_depth", 0.0))


def triads_accepted(summary: dict[str, Any]) -> int:
    return int(summary.get("triads_accepted", 0))


def zero_hits(summary: dict[str, Any]) -> int:
    return int(summary.get("zero_hits_single_depth", 0))


def degeneracy(summary: dict[str, Any]) -> dict[str, Any]:
    return {
        "anti_parallel_rejects": int(summary.get("anti_parallel_rejects", 0)),
        "exact_degenerate_outputs": int(summary.get("exact_degenerate_outputs", 0)),
        "frame_source": summary.get("frame_source"),
        "frame_model": summary.get("frame_model"),
    }


def classify_case(summary: dict[str, Any], *, min_depth2_for_permissive: float) -> str:
    hf = hit_fraction(summary)
    df = depth2_fraction(summary)
    width = width_value(summary)

    if triads_accepted(summary) == 0:
        return "invalid_no_triads"
    if hf >= 0.95 and (df is None or df >= min_depth2_for_permissive):
        return "very_permissive_family_i_ii"
    if hf >= 0.50 and (df is None or df >= min_depth2_for_permissive):
        return "permissive_family_i_ii"
    if hf >= 0.10:
        return "moderately_permissive"
    if width is not None and width <= 1.0e-3 and hf > 0.0:
        return "thin_zero_set_or_width_collapsed"
    return "restrictive_under_sample"


def run_child(
    case: SweepCase,
    args: argparse.Namespace,
) -> tuple[dict[str, Any], list[str], float]:
    exact_seed = case.seed + 1701
    command = [
        sys.executable,
        str(args.child_script),
        "--frame-model",
        "exact-strain",
        "--exact-polarization-model",
        case.polarization,
        "--exact-polarization-seed",
        str(exact_seed),
        "--seed",
        str(case.seed),
        "--samples",
        str(case.samples),
        "--tolerance",
        repr(case.tolerance),
        "--bins",
        str(args.bins),
        "--normals",
        str(args.normals),
        "--depth2-trials-per-hit",
        str(args.depth2_trials_per_hit),
        "--axis",
        str(args.axis[0]),
        str(args.axis[1]),
        str(args.axis[2]),
        "--json",
    ]
    started = time.perf_counter()
    proc = subprocess.run(
        command,
        cwd=SCRIPT_DIR.parent,
        text=True,
        capture_output=True,
        timeout=args.timeout_seconds,
        check=False,
    )
    elapsed = time.perf_counter() - started
    if proc.returncode != 0:
        return (
            {
                "error": "child_failed",
                "returncode": proc.returncode,
                "stdout_tail": proc.stdout[-1000:],
                "stderr_tail": proc.stderr[-2000:],
            },
            command,
            elapsed,
        )
    try:
        data = json.loads(proc.stdout)
    except json.JSONDecodeError as exc:
        return (
            {
                "error": "child_json_decode_failed",
                "message": str(exc),
                "stdout_tail": proc.stdout[-2000:],
                "stderr_tail": proc.stderr[-2000:],
            },
            command,
            elapsed,
        )
    return data, command, elapsed


def summarize_group(rows: list[dict[str, Any]]) -> dict[str, Any]:
    ok_rows = [row for row in rows if row.get("status") == "ok"]
    return {
        "cases": len(rows),
        "ok_cases": len(ok_rows),
        "mean_zero_hit_fraction": mean(row["metrics"]["zero_hit_fraction"] for row in ok_rows),
        "median_zero_hit_fraction": median(row["metrics"]["zero_hit_fraction"] for row in ok_rows),
        "mean_depth2_survival_fraction": mean(
            row["metrics"]["depth2_survival_fraction"]
            for row in ok_rows
            if row["metrics"]["depth2_survival_fraction"] is not None
        ),
        "mean_output_width": mean(
            row["metrics"]["estimated_output_width"]
            for row in ok_rows
            if row["metrics"]["estimated_output_width"] is not None
        ),
        "classifications": {
            label: sum(1 for row in ok_rows if row["classification"] == label)
            for label in sorted({row["classification"] for row in ok_rows})
        },
    }


def build_report(args: argparse.Namespace) -> dict[str, Any]:
    if not args.child_script.exists():
        raise FileNotFoundError(f"child harness not found: {args.child_script}")
    if args.depth2_trials_per_hit < 0:
        raise ValueError("--depth2-trials-per-hit must be nonnegative")

    cases = [
        SweepCase(tolerance=tolerance, polarization=polarization, seed=seed, samples=samples)
        for tolerance, polarization, seed, samples in itertools.product(
            args.tolerances,
            args.polarizations,
            args.seeds,
            args.sample_counts,
        )
    ]

    case_rows: list[dict[str, Any]] = []
    started = time.perf_counter()
    for case in cases:
        child_data, command, elapsed = run_child(case, args)
        row: dict[str, Any] = {
            "case": {
                "tolerance": case.tolerance,
                "polarization": case.polarization,
                "seed": case.seed,
                "samples": case.samples,
            },
            "elapsed_seconds": elapsed,
        }
        if args.print_child_commands:
            row["child_command"] = command
        if "error" in child_data:
            row.update({"status": "failed", "child": child_data})
            case_rows.append(row)
            continue

        classification = classify_case(child_data, min_depth2_for_permissive=0.50)
        row.update(
            {
                "status": "ok",
                "classification": classification,
                "metrics": {
                    "triads_accepted": triads_accepted(child_data),
                    "zero_hits": zero_hits(child_data),
                    "zero_hit_fraction": hit_fraction(child_data),
                    "family_i_hits": int(child_data.get("family_i_hits", 0)),
                    "family_ii_hits": int(child_data.get("family_ii_hits", 0)),
                    "both_family_hits": int(child_data.get("both_family_hits", 0)),
                    "depth2_continuation_hits": child_data.get("depth2_continuation_hits"),
                    "depth2_survival_fraction": depth2_fraction(child_data),
                    "estimated_output_width": width_value(child_data),
                    "min_single_residual": child_data.get("min_single_residual"),
                    "median_single_residual": child_data.get("median_single_residual"),
                    "p95_single_residual": child_data.get("p95_single_residual"),
                },
                "degeneracy": degeneracy(child_data),
            }
        )
        case_rows.append(row)

    by_polarization: dict[str, list[dict[str, Any]]] = {}
    by_tolerance: dict[str, list[dict[str, Any]]] = {}
    by_samples: dict[str, list[dict[str, Any]]] = {}
    for row in case_rows:
        case = row["case"]
        by_polarization.setdefault(case["polarization"], []).append(row)
        by_tolerance.setdefault(f"{case['tolerance']:.12g}", []).append(row)
        by_samples.setdefault(str(case["samples"]), []).append(row)

    ok_rows = [row for row in case_rows if row.get("status") == "ok"]
    permissive_rows = [
        row
        for row in ok_rows
        if row.get("classification")
        in {"very_permissive_family_i_ii", "permissive_family_i_ii", "moderately_permissive"}
    ]
    very_permissive_rows = [
        row for row in ok_rows if row.get("classification") == "very_permissive_family_i_ii"
    ]

    promotion = False
    return {
        "scope": "local_exact_strain_threshold_polarization_sweep_diagnostic_only",
        "promotion": promotion,
        "clay_promoted": False,
        "family_i_ii_current_formulation_promoted": False,
        "parameters": {
            "child_script": str(args.child_script),
            "tolerances": args.tolerances,
            "polarizations": args.polarizations,
            "seeds": args.seeds,
            "sample_counts": args.sample_counts,
            "normals": args.normals,
            "bins": args.bins,
            "depth2_trials_per_hit": args.depth2_trials_per_hit,
            "axis": list(args.axis),
            "timeout_seconds": args.timeout_seconds,
        },
        "summary": {
            "cases_requested": len(cases),
            "cases_ok": len(ok_rows),
            "cases_failed": len(case_rows) - len(ok_rows),
            "elapsed_seconds": time.perf_counter() - started,
            "mean_zero_hit_fraction": mean(
                row["metrics"]["zero_hit_fraction"] for row in ok_rows
            ),
            "mean_depth2_survival_fraction": mean(
                row["metrics"]["depth2_survival_fraction"]
                for row in ok_rows
                if row["metrics"]["depth2_survival_fraction"] is not None
            ),
            "mean_output_width": mean(
                row["metrics"]["estimated_output_width"]
                for row in ok_rows
                if row["metrics"]["estimated_output_width"] is not None
            ),
            "permissive_or_moderate_cases": len(permissive_rows),
            "very_permissive_cases": len(very_permissive_rows),
            "current_family_i_ii_formulation_permissive": bool(permissive_rows),
            "diagnostic_conclusion": (
                "current Family-I/II exact-strain formulation is permissive under "
                "at least one sweep case; strengthen propagated polarization/coherence"
                if permissive_rows
                else "current sweep did not find permissiveness; increase samples/grid before inference"
            ),
        },
        "groups": {
            "by_polarization": {
                key: summarize_group(rows) for key, rows in sorted(by_polarization.items())
            },
            "by_tolerance": {
                key: summarize_group(rows) for key, rows in sorted(by_tolerance.items())
            },
            "by_samples": {key: summarize_group(rows) for key, rows in sorted(by_samples.items())},
        },
        "cases": case_rows,
    }


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    report = build_report(args)
    rendered = json.dumps(report, indent=2, sort_keys=True)
    if args.json_output is not None:
        args.json_output.parent.mkdir(parents=True, exist_ok=True)
        args.json_output.write_text(rendered + "\n", encoding="utf-8")
    print(rendered)
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except KeyboardInterrupt:
        raise SystemExit(130)
