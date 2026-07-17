#!/usr/bin/env python3
"""Compare frozen-packet coercivity traces under a fixed, non-causal protocol.

This tool does not fit thresholds, optimize profiles, or infer a Navier--
Stokes theorem.  It applies the same post-peak, adjacent-window Gamma rule to
every durable finite-Galerkin receipt and reports whether the exact coercivity
factorization was available at the sampled checkpoints.
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any


FACTOR_KEYS = {
    "forcing": "forcing_to_viscous_gradient_ratio",
    "geometry": "packet_to_gradient_ratio",
    "alignment": "positive_nonlinear_alignment",
}


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("receipts", nargs="+", type=Path)
    parser.add_argument("--factor-decline-fraction", type=float, default=0.8)
    parser.add_argument("--output-json", type=Path)
    return parser.parse_args()


def first_index(values: list[float], predicate: Any) -> int | None:
    for index, value in enumerate(values):
        if predicate(value):
            return index
    return None


def number(value: Any) -> float | None:
    if isinstance(value, (int, float)) and math.isfinite(float(value)):
        return float(value)
    return None


def trace_summary(path: Path, decline_fraction: float) -> dict[str, Any]:
    receipt = json.loads(path.read_text())
    evolution = receipt.get("finite_galerkin_evolution")
    if not isinstance(evolution, dict):
        raise ValueError(f"{path}: no finite_galerkin_evolution receipt")
    checkpoints = evolution.get("checkpoints", [])
    if not checkpoints:
        raise ValueError(f"{path}: no checkpoints")
    times = [float(row["time"]) for row in checkpoints]
    packets = [float(row["frozen_initial_packet"]) for row in checkpoints]
    gamma = [float(row["frozen_initial_packet_positive_coercivity_ratio"]) for row in checkpoints]
    peak_index = max(range(len(packets)), key=packets.__getitem__)
    focus_start_time = float(evolution.get("mechanism_trace_start_fraction_requested", 0.0)) * float(
        evolution["actual_window_time"]
    )
    focus_start_index = min(range(len(times)), key=lambda index: abs(times[index] - focus_start_time))
    windows = evolution.get("frozen_packet_coercivity_windows", [])
    postpeak_window = next((
        row for row in windows
        if float(row["start_time"]) >= times[peak_index]
        and number(row.get("positive_coercivity_ratio")) is not None
        and float(row["positive_coercivity_ratio"]) <= 1.0
    ), None)
    postpeak_sample = first_index(
        gamma, lambda value: value <= 1.0,
    )
    if postpeak_sample is not None and postpeak_sample <= peak_index:
        postpeak_sample = first_index(gamma[peak_index + 1:], lambda value: value <= 1.0)
        postpeak_sample = None if postpeak_sample is None else peak_index + 1 + postpeak_sample
    factor_rows = [row.get("frozen_initial_packet_coercivity_factors") for row in checkpoints]
    factor_available = all(isinstance(row, dict) for row in factor_rows)
    factors: dict[str, Any] = {"status": "unavailable_in_legacy_receipt"}
    if factor_available:
        factors = {"status": "available", "decline_fraction": decline_fraction, "components": {}}
        for name, key in FACTOR_KEYS.items():
            values = [number(row.get(key)) for row in factor_rows]
            if any(value is None for value in values):
                factors["components"][name] = {"status": "missing_or_nonfinite"}
                continue
            clean = [float(value) for value in values if value is not None]
            factor_peak_index = max(range(peak_index + 1), key=clean.__getitem__)
            prepeak_max = clean[factor_peak_index]
            threshold = decline_fraction * prepeak_max
            decline_after_factor_peak = next(
                (index for index in range(factor_peak_index + 1, len(clean)) if clean[index] <= threshold),
                None,
            )
            decline = next((index for index in range(peak_index + 1, len(clean)) if clean[index] <= threshold), None)
            factors["components"][name] = {
                "factor_prepeak_maximum_time": times[factor_peak_index],
                "prepeak_maximum": prepeak_max,
                "decline_threshold": threshold,
                "first_decline_after_factor_peak_time": (
                    times[decline_after_factor_peak] if decline_after_factor_peak is not None else None
                ),
                "first_postpeak_decline_time": times[decline] if decline is not None else None,
                "focused_window_start_time": times[focus_start_index],
                "value_at_focused_window_start": clean[focus_start_index],
                "value_at_peak": clean[peak_index],
                "focused_window_start_to_packet_peak_ratio": (
                    clean[peak_index] / clean[focus_start_index]
                    if abs(clean[focus_start_index]) > 1.0e-30 else None
                ),
                "value_at_endpoint": clean[-1],
            }
        residuals = [number(row.get("positive_coercivity_factorisation_residual")) for row in factor_rows]
        if all(value is not None for value in residuals):
            factors["maximum_absolute_factorisation_residual"] = max(abs(float(value)) for value in residuals if value is not None)
    initial_packet = packets[0]
    balance_residual = (
        packets[-1] - initial_packet
        - float(evolution["integrated_frozen_initial_packet_nonlinear_input"])
        + float(evolution["integrated_frozen_initial_packet_viscous_loss"])
    )
    return {
        "receipt": str(path),
        "contract": receipt.get("contract"),
        "authority": receipt.get("authority"),
        "backend": evolution.get("backend"),
        "trace_count": evolution.get("mechanism_trace_count_requested"),
        "endpoint_frozen_packet_ratio": evolution.get("frozen_initial_packet_recurrence_ratio"),
        "peak": {"time": times[peak_index], "packet": packets[peak_index]},
        "focused_window_start_time": times[focus_start_index],
        "postpeak_gamma_sample_downcrossing_time": times[postpeak_sample] if postpeak_sample is not None else None,
        "postpeak_gamma_window_downcrossing": postpeak_window,
        "frozen_balance_trapezoid_residual": balance_residual,
        "factors": factors,
        "warning": (
            "finite-Galerkin descriptive comparison only; shape metrics are secondary and no causal "
            "ordering is inferred from this report"
        ),
    }


def main() -> None:
    args = parse_args()
    if not 0.0 < args.factor_decline_fraction < 1.0:
        raise ValueError("--factor-decline-fraction must lie in (0, 1)")
    summaries = [trace_summary(path, args.factor_decline_fraction) for path in args.receipts]
    payload = {
        "contract": "preregistered_frozen_packet_coercivity_trace_comparison_nonpromoting",
        "authority": {"empirical_non_promoting": True, "theorem_authority": False, "clay_authority": False},
        "factor_decline_fraction": args.factor_decline_fraction,
        "event_rule": "first adjacent positive-input/viscous-loss window starting at or after the sampled frozen-packet peak with ratio <= 1",
        "traces": summaries,
    }
    rendered = json.dumps(payload, indent=2, sort_keys=True) + "\n"
    if args.output_json is not None:
        args.output_json.parent.mkdir(parents=True, exist_ok=True)
        args.output_json.write_text(rendered)
    print(rendered, end="")


if __name__ == "__main__":
    main()
