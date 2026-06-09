#!/usr/bin/env python3
"""Sweep finite NS kappa-bias proxy profiles.

This pure-stdlib harness wraps ``ns_kappa_bias_variational_harness`` in-process
and checks whether finite profile choices can keep a positive
``lambda*(kappa^2 - 1/2)`` bias after the one-step stationarity proxy.

It is a local diagnostic only.  It does not construct a Type-I blowup measure,
does not prove an Abel triadic defect theorem, and does not promote Clay status.
"""

from __future__ import annotations

import argparse
import importlib.util
import json
import math
import statistics
import sys
from dataclasses import dataclass
from pathlib import Path
from types import ModuleType
from typing import Any, Sequence


SCRIPT_DIR = Path(__file__).resolve().parent
VARIATIONAL_PATH = SCRIPT_DIR / "ns_kappa_bias_variational_harness.py"


@dataclass(frozen=True)
class SweepProfile:
    name: str
    samples: int
    top_fraction: float
    coverage_normals: int
    lrt_candidate_multiplier: float


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--seed", type=int, default=20260608)
    parser.add_argument(
        "--samples",
        type=int,
        default=None,
        help="Override per-profile sample count.  Quick mode still clamps this for 10s runs.",
    )
    parser.add_argument("--quick", action="store_true", help="Use a 10s-safe compact sweep.")
    parser.add_argument("--json-output", type=Path, default=None)
    parser.add_argument("--json", action="store_true", help="Emit compact JSON only.")
    return parser.parse_args(argv)


def load_variational() -> ModuleType:
    if not VARIATIONAL_PATH.exists():
        raise FileNotFoundError(f"required harness missing: {VARIATIONAL_PATH}")
    spec = importlib.util.spec_from_file_location("ns_kappa_bias_variational_harness", VARIATIONAL_PATH)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"failed to load variational harness spec: {VARIATIONAL_PATH}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def profiles(quick: bool, sample_override: int | None) -> list[SweepProfile]:
    if quick:
        base = [
            SweepProfile("tight_tail_low_coverage", 2400, 0.02, 64, 4.0),
            SweepProfile("standard_tail", 2600, 0.05, 96, 8.0),
            SweepProfile("broad_tail", 2600, 0.10, 96, 6.0),
            SweepProfile("coverage_heavy", 2200, 0.05, 160, 10.0),
            SweepProfile("very_broad_tail", 2400, 0.20, 96, 4.0),
        ]
    else:
        base = [
            SweepProfile("tight_tail_low_coverage", 6000, 0.02, 128, 5.0),
            SweepProfile("standard_tail", 7000, 0.05, 192, 8.0),
            SweepProfile("broad_tail", 7000, 0.10, 192, 6.0),
            SweepProfile("coverage_heavy", 6000, 0.05, 256, 12.0),
            SweepProfile("very_broad_tail", 6500, 0.20, 192, 4.0),
            SweepProfile("micro_tail", 6500, 0.01, 192, 10.0),
            SweepProfile("lrt_candidate_rich", 6000, 0.05, 224, 16.0),
        ]
    if sample_override is None:
        return base
    max_samples = 3500 if quick else sample_override
    override = max(200, min(sample_override, max_samples))
    return [
        SweepProfile(item.name, override, item.top_fraction, item.coverage_normals, item.lrt_candidate_multiplier)
        for item in base
    ]


def finite(value: Any) -> float | None:
    if isinstance(value, (int, float)) and math.isfinite(float(value)):
        return float(value)
    return None


def run_profile(module: ModuleType, profile: SweepProfile, seed: int) -> dict[str, Any]:
    args = argparse.Namespace(
        samples=profile.samples,
        seed=seed,
        top_fraction=profile.top_fraction,
        coverage_normals=profile.coverage_normals,
        lrt_candidate_multiplier=profile.lrt_candidate_multiplier,
        json_output=None,
        json=True,
    )
    raw = module.run(args)

    baseline = finite(raw.get("baseline_all_mean_bias"))
    stationary = finite(raw.get("stationary_proxy_mean_bias"))
    lrt_stationary = finite(raw.get("lrt_and_stationary_proxy_mean_bias"))
    lrt = finite(raw.get("lrt_proxy_mean_bias"))
    unconstrained = finite(raw.get("unconstrained_max_mean_bias"))
    stationary_candidates = [x for x in (stationary, lrt_stationary) if x is not None]
    worst_stationary = max(stationary_candidates) if stationary_candidates else None

    return {
        "name": profile.name,
        "seed": seed,
        "samples": profile.samples,
        "accepted_samples": raw.get("accepted_samples"),
        "top_fraction": profile.top_fraction,
        "coverage_normals": profile.coverage_normals,
        "lrt_candidate_multiplier": profile.lrt_candidate_multiplier,
        "baseline_all_mean_bias": baseline,
        "neutral_baseline_drift_abs": abs(baseline) if baseline is not None else None,
        "unconstrained_mean_bias": unconstrained,
        "lrt_proxy_mean_bias": lrt,
        "stationary_proxy_mean_bias": stationary,
        "lrt_and_stationary_proxy_mean_bias": lrt_stationary,
        "worst_stationary_proxy_mean_bias": worst_stationary,
        "stationarity_erases_unconstrained_bias": (
            None
            if unconstrained is None or worst_stationary is None
            else worst_stationary < 0.25 * unconstrained
        ),
        "coverage_score": raw.get("coverage_score"),
        "selected_counts": raw.get("selected_counts"),
        "promotion": raw.get("promotion"),
    }


def quantiles(values: Sequence[float]) -> dict[str, float | None]:
    data = sorted(x for x in values if math.isfinite(x))
    if not data:
        return {"count": 0, "min": None, "median": None, "mean": None, "max": None}
    return {
        "count": len(data),
        "min": data[0],
        "median": statistics.median(data),
        "mean": statistics.fmean(data),
        "max": data[-1],
    }


def run(args: argparse.Namespace) -> dict[str, Any]:
    module = load_variational()
    plan = profiles(args.quick, args.samples)
    rows = [run_profile(module, profile, args.seed + 7919 * index) for index, profile in enumerate(plan)]

    stationary_values = [
        row["worst_stationary_proxy_mean_bias"]
        for row in rows
        if isinstance(row.get("worst_stationary_proxy_mean_bias"), float)
    ]
    baseline_drifts = [
        row["neutral_baseline_drift_abs"]
        for row in rows
        if isinstance(row.get("neutral_baseline_drift_abs"), float)
    ]
    positive_stationary_rows = [
        row for row in rows if isinstance(row.get("worst_stationary_proxy_mean_bias"), float)
        and row["worst_stationary_proxy_mean_bias"] > 0.0
    ]
    worst_positive = max(
        positive_stationary_rows,
        key=lambda row: row["worst_stationary_proxy_mean_bias"],
        default=None,
    )
    max_baseline_drift = max(baseline_drifts) if baseline_drifts else None

    return {
        "harness": "ns_kappa_bias_profile_sweep",
        "scope": "finite_s2_profile_sensitivity_not_pde_proof",
        "wrapped_harness": str(VARIATIONAL_PATH),
        "quick": bool(args.quick),
        "seed": args.seed,
        "profile_count": len(rows),
        "profiles": rows,
        "summary": {
            "worst_positive_stationary_proxy": worst_positive,
            "positive_stationary_profile_count": len(positive_stationary_rows),
            "stationary_proxy_quantiles": quantiles(stationary_values),
            "max_neutral_baseline_drift_abs": max_baseline_drift,
            "baseline_drift_quantiles": quantiles(baseline_drifts),
            "neutral_baseline_drift_alert": (
                None if max_baseline_drift is None else max_baseline_drift > 0.02
            ),
        },
        "interpretation": (
            "Finite profile sensitivity only: positive top-tail/LRT bias is easy "
            "to select, but the one-step stationarity proxy is the relevant "
            "falsification signal.  Type-I/self-similar kappa-bias remains open."
        ),
        "promotion": {
            "clay": False,
            "pde_gate_closed": False,
            "reason": "profile sweep wraps finite proxy harness only",
        },
    }


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    result = run(args)
    if args.json_output is not None:
        args.json_output.parent.mkdir(parents=True, exist_ok=True)
        args.json_output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    if args.json:
        print(json.dumps(result, sort_keys=True))
    else:
        print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
