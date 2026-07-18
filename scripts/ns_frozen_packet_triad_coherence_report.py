#!/usr/bin/env python3
"""Compare sampled convolution-atom coherence on fixed frozen-packet traces.

This consumes only receipts produced with
``--triad-coherence-samples-per-output``.  It does not choose a profile,
fit a threshold, or infer a continuum cancellation theorem.  Its sole job is
to keep the four pre-registered traces on one event surface: focused start,
sampled packet peak, and the first post-peak adjacent Gamma window at most one.
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any


COHERENCE_KEYS = {
    "raw_forcing": "raw_triadic_forcing_to_viscous_gradient_ratio",
    "vector": "inter_triad_vector_coherence",
    "packet_alignment": "packet_direction_alignment_from_exact_resultant",
    "geometry": "packet_to_gradient_ratio",
    "phase": "scalar_phase_coherence",
    "sign": "scalar_real_sign_coherence",
    "positive_transfer_efficiency": "positive_transfer_efficiency",
}


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("receipts", nargs="+", type=Path)
    parser.add_argument("--output-json", type=Path)
    return parser.parse_args()


def finite(value: Any) -> float | None:
    return float(value) if isinstance(value, (int, float)) and math.isfinite(float(value)) else None


def nearest_index(times: list[float], target: float) -> int:
    return min(range(len(times)), key=lambda index: abs(times[index] - target))


def selected_values(row: dict[str, Any]) -> dict[str, Any]:
    coherence = row.get("frozen_initial_packet_triad_coherence")
    if not isinstance(coherence, dict) or coherence.get("status") != "sampled_oriented_convolution_atoms":
        return {"status": "unavailable"}
    values: dict[str, Any] = {
        "status": "available",
        "atom_convention": coherence.get("atom_convention"),
    }
    for name, key in COHERENCE_KEYS.items():
        values[name] = finite(coherence.get(key))
        interval = coherence.get(f"{key}_nominal_95_percent_interval")
        if interval is not None:
            values[f"{name}_nominal_95_percent_interval"] = interval
    return values


def ratio(later: dict[str, Any], earlier: dict[str, Any], key: str) -> float | None:
    numerator, denominator = finite(later.get(key)), finite(earlier.get(key))
    if numerator is None or denominator is None or abs(denominator) <= 1.0e-30:
        return None
    return numerator / denominator


def summarize(path: Path) -> dict[str, Any]:
    receipt = json.loads(path.read_text())
    evolution = receipt.get("finite_galerkin_evolution")
    if not isinstance(evolution, dict):
        raise ValueError(f"{path}: no finite_galerkin_evolution")
    rows = evolution.get("checkpoints")
    if not isinstance(rows, list) or not rows:
        raise ValueError(f"{path}: no checkpoints")
    times = [float(row["time"]) for row in rows]
    packets = [float(row["frozen_initial_packet"]) for row in rows]
    peak_index = max(range(len(rows)), key=packets.__getitem__)
    focus_time = float(evolution.get("mechanism_trace_start_fraction_requested", 0.0)) * float(evolution["actual_window_time"])
    focus_index = nearest_index(times, focus_time)
    downcrossing = next((
        window for window in evolution.get("frozen_packet_coercivity_windows", [])
        if float(window["start_time"]) >= times[peak_index]
        and finite(window.get("positive_coercivity_ratio")) is not None
        and float(window["positive_coercivity_ratio"]) <= 1.0
    ), None)
    gamma_index = nearest_index(times, float(downcrossing["end_time"])) if downcrossing else None
    event_indices = {"focus": focus_index, "peak": peak_index}
    if gamma_index is not None:
        event_indices["gamma_downcrossing_sample"] = gamma_index
    events = {
        name: {
            "time": times[index],
            "packet": packets[index],
            "gamma": finite(rows[index].get("frozen_initial_packet_positive_coercivity_ratio")),
            "coherence": selected_values(rows[index]),
        }
        for name, index in event_indices.items()
    }
    focus, peak = events["focus"]["coherence"], events["peak"]["coherence"]
    focus_to_peak = {
        name: ratio(peak, focus, name)
        for name in COHERENCE_KEYS
    }
    return {
        "receipt": str(path),
        "authority": receipt.get("authority"),
        "events": events,
        "postpeak_gamma_window": downcrossing,
        "focus_to_peak_retention": focus_to_peak,
        "warning": (
            "finite-Galerkin descriptive comparison only. Oriented atom coherence distinguishes sampled "
            "convolution-atom cancellation from rotation of the exact resultant, but it is not a causal or continuum claim."
        ),
    }


def main() -> None:
    args = parse_args()
    payload = {
        "contract": "frozen_packet_oriented_atom_coherence_comparison_nonpromoting",
        "authority": {"empirical_non_promoting": True, "theorem_authority": False, "clay_authority": False},
        "event_rule": "focused start, sampled frozen-packet peak, then first post-peak adjacent positive-input/viscous-loss window at most one",
        "traces": [summarize(path) for path in args.receipts],
    }
    rendered = json.dumps(payload, indent=2, sort_keys=True) + "\n"
    if args.output_json is not None:
        args.output_json.parent.mkdir(parents=True, exist_ok=True)
        args.output_json.write_text(rendered)
    print(rendered, end="")


if __name__ == "__main__":
    main()
