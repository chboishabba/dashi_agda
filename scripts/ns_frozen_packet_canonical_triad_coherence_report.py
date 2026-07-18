#!/usr/bin/env python3
"""Compare canonical-orbit packet-transfer cancellation on fixed traces.

This consumes finite-Galerkin receipts produced with
``--canonical-triad-samples-per-output``.  Each reported contribution first
aggregates every sampled ordered convolution atom over its input swaps, output
legs, and reality partner.  The script is deliberately descriptive: it does
not choose profiles, tune a threshold, or infer a continuum cancellation law.
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any


CANONICAL_KEYS = {
    "canonical_coherence": "canonical_real_transfer_coherence",
    "positive_efficiency": "canonical_positive_transfer_efficiency",
    "unsigned_envelope": "estimated_unsigned_canonical_packet_transfer_envelope",
    "internal_atom_retention": "internal_ordered_atom_cancellation_ratio",
    "ordered_atom_envelope": "estimated_unsigned_ordered_atom_packet_transfer_envelope",
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
    coherence = row.get("frozen_initial_packet_canonical_triad_coherence")
    if not isinstance(coherence, dict) or coherence.get("status") != "sampled_canonical_reality_orbits":
        return {"status": "unavailable"}
    exact_pairing = finite(coherence.get("exact_packet_pairing_real"))
    estimated_pairing = finite(coherence.get("estimated_regrouped_packet_pairing"))
    values: dict[str, Any] = {
        "status": "available",
        "orbit_convention": coherence.get("orbit_convention"),
        "exact_packet_pairing_real": exact_pairing,
        "estimated_regrouped_packet_pairing": estimated_pairing,
    }
    if exact_pairing is not None and estimated_pairing is not None and abs(exact_pairing) > 1.0e-30:
        values["regrouped_packet_pairing_relative_error"] = (estimated_pairing - exact_pairing) / exact_pairing
    else:
        values["regrouped_packet_pairing_relative_error"] = None
    for name, key in CANONICAL_KEYS.items():
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


def log_ratio(later: float | None, earlier: float | None) -> float | None:
    if later is None or earlier is None or later <= 0.0 or earlier <= 0.0:
        return None
    return math.log(later / earlier)


def canonical_log_attribution(focus: dict[str, Any], peak: dict[str, Any]) -> dict[str, Any]:
    """Describe the finite focus-to-peak change without fitting a mechanism.

    ``Gamma = E_+ A / V`` algebraically when the canonical envelope is exact.
    Here ``A`` is sampled, so the returned closure residual deliberately
    measures the Monte-Carlo/finite-window mismatch rather than hiding it.
    """
    focus_canonical = focus["canonical"]
    peak_canonical = peak["canonical"]
    log_gamma = log_ratio(finite(peak.get("gamma")), finite(focus.get("gamma")))
    log_efficiency = log_ratio(
        finite(peak_canonical.get("positive_efficiency")),
        finite(focus_canonical.get("positive_efficiency")),
    )
    log_envelope = log_ratio(
        finite(peak_canonical.get("unsigned_envelope")),
        finite(focus_canonical.get("unsigned_envelope")),
    )
    log_viscous = log_ratio(finite(peak.get("viscous_rate")), finite(focus.get("viscous_rate")))
    reconstructed = None
    residual = None
    if log_efficiency is not None and log_envelope is not None and log_viscous is not None:
        reconstructed = log_efficiency + log_envelope - log_viscous
        if log_gamma is not None:
            residual = log_gamma - reconstructed
    return {
        "log_positive_coercivity_ratio_change": log_gamma,
        "log_canonical_positive_efficiency_change": log_efficiency,
        "log_unsigned_canonical_envelope_change": log_envelope,
        "log_viscous_rate_change": log_viscous,
        "reconstructed_log_change_from_sampled_canonical_factors": reconstructed,
        "log_factorization_closure_residual": residual,
        "warning": (
            "The unsigned canonical envelope is Monte-Carlo estimated. The closure residual is therefore an "
            "estimator diagnostic, not an algebraic defect in the exact packet balance."
        ),
    }


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
            "viscous_rate": finite(rows[index].get("frozen_initial_packet_viscous_rate")),
            "canonical": selected_values(rows[index]),
        }
        for name, index in event_indices.items()
    }
    focus, peak = events["focus"]["canonical"], events["peak"]["canonical"]
    return {
        "receipt": str(path),
        "authority": receipt.get("authority"),
        "events": events,
        "postpeak_gamma_window": downcrossing,
        "focus_to_peak_retention": {name: ratio(peak, focus, name) for name in CANONICAL_KEYS},
        "focus_to_peak_log_attribution": canonical_log_attribution(events["focus"], events["peak"]),
        "warning": (
            "finite-Galerkin descriptive comparison only. Canonical orbit envelopes are sampled, and the exact packet "
            "pairing is retained separately. This is neither a certified bound nor a continuum triad-cancellation theorem."
        ),
    }


def main() -> None:
    args = parse_args()
    payload = {
        "contract": "frozen_packet_canonical_reality_orbit_coherence_comparison_nonpromoting",
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
