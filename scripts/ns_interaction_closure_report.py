#!/usr/bin/env python3
"""Summarise exact finite interaction-closure receipts without promotion.

The report deliberately separates two capture questions:

* how much target-shell modal activity the selected output carrier covers; and
* how concentrated the unordered convolution interactions are inside it.

A broad interaction distribution on a low-capture output carrier is evidence
for proliferation, but is not classified as a full-shell closure theorem.
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any

import numpy as np


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("receipt", type=Path)
    parser.add_argument("--output-json", type=Path)
    return parser.parse_args()


def interaction_key(row: dict[str, Any]) -> tuple[Any, ...]:
    return (
        tuple(row["output"]),
        tuple(row["inputs"][0]),
        tuple(row["inputs"][1]),
    )


def jaccard(left: set[tuple[Any, ...]], right: set[tuple[Any, ...]]) -> float:
    union = left | right
    return float(len(left & right) / len(union)) if union else 1.0


def linear_fit(x: np.ndarray, y: np.ndarray) -> dict[str, float]:
    design = np.column_stack((np.ones_like(x), x))
    coefficient, *_ = np.linalg.lstsq(design, y, rcond=None)
    prediction = design @ coefficient
    residual = y - prediction
    total = y - np.mean(y)
    return {
        "intercept": float(coefficient[0]),
        "slope": float(coefficient[1]),
        "rmse_log_weight": float(np.sqrt(np.mean(residual ** 2))),
        "r_squared": float(1.0 - np.sum(residual ** 2) / np.sum(total ** 2))
        if np.sum(total ** 2) > 0.0 else 1.0,
    }


def truncated_rank_fits(snapshot: dict[str, Any]) -> dict[str, Any]:
    weights = np.asarray(
        [row["absolute_transfer"] for row in snapshot.get("largest_interactions", [])],
        dtype=np.float64,
    )
    weights = weights[weights > 0.0]
    if weights.size < 8:
        return {"status": "insufficient_retained_positive_weights"}
    ranks = np.arange(1, weights.size + 1, dtype=np.float64)
    log_weights = np.log(weights)
    bands = []
    for lower, requested_upper in ((1, 32), (33, 128), (129, 512)):
        upper = min(requested_upper, int(weights.size))
        if upper < lower or upper - lower + 1 < 8:
            continue
        selection = slice(lower - 1, upper)
        fit = linear_fit(np.log(ranks[selection]), log_weights[selection])
        bands.append({
            "rank_min": lower,
            "rank_max": upper,
            "local_power_exponent_alpha": -fit["slope"],
            **fit,
        })
    power = linear_fit(np.log(ranks), log_weights)
    exponential = linear_fit(ranks, log_weights)
    stretched_candidates = []
    for beta in np.linspace(0.2, 1.5, 66):
        fit = linear_fit(ranks ** beta, log_weights)
        stretched_candidates.append((fit["rmse_log_weight"], float(beta), fit))
    _, beta, stretched = min(stretched_candidates, key=lambda row: row[0])
    return {
        "status": "descriptive_truncated_fit_only",
        "warning": (
            "fits use only retained leading interactions; they neither certify the omitted tail "
            "nor justify extrapolated M90/M99 values"
        ),
        "retained_weight_count": int(weights.size),
        "power_law": {"alpha": -power["slope"], **power},
        "exponential": exponential,
        "best_stretched_exponential": {"beta": beta, **stretched},
        "local_power_bands": bands,
    }


def retained_geometric_structure(snapshot: dict[str, Any]) -> dict[str, Any]:
    rows = snapshot.get("largest_interactions", [])
    retained_total = sum(float(row["absolute_transfer"]) for row in rows)
    if retained_total <= 0.0:
        return {"status": "no_positive_retained_activity"}

    shell_pairs: dict[tuple[int, int], float] = {}
    locality = {"local_ratio_lt_2": 0.0, "moderate_ratio_2_to_4": 0.0, "nonlocal_ratio_ge_4": 0.0}
    weighted_angle = 0.0
    angled_weight = 0.0
    for row in rows:
        left, right = row["inputs"]
        weight = float(row["absolute_transfer"])
        left_norm = math.sqrt(sum(float(value) ** 2 for value in left))
        right_norm = math.sqrt(sum(float(value) ** 2 for value in right))
        left_shell = math.floor(math.log2(left_norm)) if left_norm > 0.0 else -99
        right_shell = math.floor(math.log2(right_norm)) if right_norm > 0.0 else -99
        shell_pair = tuple(sorted((left_shell, right_shell)))
        shell_pairs[shell_pair] = shell_pairs.get(shell_pair, 0.0) + weight
        ratio = max(left_norm, right_norm) / max(1.0e-30, min(left_norm, right_norm))
        if ratio < 2.0:
            locality["local_ratio_lt_2"] += weight
        elif ratio < 4.0:
            locality["moderate_ratio_2_to_4"] += weight
        else:
            locality["nonlocal_ratio_ge_4"] += weight
        if left_norm > 0.0 and right_norm > 0.0:
            cosine = sum(float(a) * float(b) for a, b in zip(left, right)) / (left_norm * right_norm)
            weighted_angle += math.acos(max(-1.0, min(1.0, cosine))) * weight
            angled_weight += weight
    return {
        "status": "retained_rows_only",
        "retained_full_activity_capture": snapshot["retained_absolute_activity_capture"],
        "shell_pair_activity_fractions": [
            {"input_shell_pair": list(pair), "fraction": activity / retained_total}
            for pair, activity in sorted(shell_pairs.items(), key=lambda item: item[1], reverse=True)
        ],
        "scale_locality_activity_fractions": {
            name: activity / retained_total for name, activity in locality.items()
        },
        "weighted_mean_input_angle_radians": weighted_angle / angled_weight if angled_weight else None,
    }


def snapshot_summary(snapshot: dict[str, Any]) -> dict[str, Any]:
    if "nonzero_interaction_count" in snapshot:
        eligible = int(snapshot["nonzero_interaction_count"])
        eligible_authority = "exact_nonzero_count"
    elif snapshot["retained_absolute_activity_capture"] >= 1.0 - 1.0e-12:
        eligible = sum(
            row["absolute_transfer"] > 0.0 for row in snapshot.get("largest_interactions", [])
        )
        eligible_authority = "inferred_exact_from_complete_retained_activity"
    else:
        eligible = int(snapshot["interaction_count"])
        eligible_authority = "kinematic_interaction_count_upper_bound"
    neff1 = float(snapshot["effective_interaction_support"])
    neff2 = snapshot.get("inverse_participation_effective_support")
    return {
        "step": snapshot["step"],
        "time": snapshot["time"],
        "analysed_output_mode_count": snapshot["analysed_output_mode_count"],
        "target_shell_output_mode_count": snapshot["target_shell_output_mode_count"],
        "output_modal_activity_capture": snapshot["analysed_output_modal_activity_capture"],
        "output_modal_activity_m50": snapshot.get("output_modal_activity_m50"),
        "output_modal_activity_m90": snapshot.get("output_modal_activity_m90"),
        "output_modal_activity_m99": snapshot.get("output_modal_activity_m99"),
        "signed_reconstruction_error": snapshot["signed_reconstruction_error"],
        "eligible_interaction_count": eligible,
        "eligible_interaction_count_authority": eligible_authority,
        "m50": snapshot["m50"],
        "m90": snapshot["m90"],
        "m99": snapshot["m99"],
        "retained_count": snapshot["retained_interaction_count"],
        "retained_capture": snapshot["retained_absolute_activity_capture"],
        "shannon_entropy": snapshot["shannon_entropy"],
        "shannon_effective_support": neff1,
        "inverse_participation_effective_support": neff2,
        "shannon_support_fraction": neff1 / eligible if eligible else 0.0,
        "inverse_participation_support_fraction": (
            float(neff2) / eligible if neff2 is not None and eligible else None
        ),
        "designed_graph_capture": snapshot["designed_interaction_absolute_capture"],
        "dominant_set_overlap": snapshot.get("dominant_set_overlap"),
        "selected_output_mode_overlap": snapshot.get("selected_output_mode_overlap"),
        "rank_fit": truncated_rank_fits(snapshot),
        "retained_geometric_structure": retained_geometric_structure(snapshot),
    }


def classify(summaries: list[dict[str, Any]]) -> dict[str, Any]:
    if not summaries:
        return {"regime": "no_closure_snapshots"}
    endpoint = summaries[-1]
    output_capture = float(endpoint["output_modal_activity_capture"])
    eligible = max(1, int(endpoint["eligible_interaction_count"]))
    m90_fraction = float(endpoint["m90"]) / eligible
    effective_fraction = float(endpoint["shannon_support_fraction"])
    if endpoint["m90"] <= 64:
        local_regime = "sparse_selected_output_carrier"
    elif m90_fraction < 0.10 and effective_fraction < 0.10:
        local_regime = "structured_broad_selected_output_carrier"
    else:
        local_regime = "effectively_dense_selected_output_carrier"
    overlap = endpoint.get("dominant_set_overlap") or {}
    top90_overlap = (overlap.get("top90") or {}).get("to_previous")
    retained_overlap = (overlap.get("top_retained") or {}).get("to_previous")
    overlap_value = top90_overlap if top90_overlap is not None else retained_overlap
    if overlap_value is None:
        temporal_regime = "temporal_persistence_unclassified"
    elif overlap_value < 0.20:
        temporal_regime = "strong_dominant_set_switching"
    elif overlap_value < 0.60:
        temporal_regime = "partial_dominant_set_switching"
    else:
        temporal_regime = "persistent_dominant_set"
    full_shell_regime = (
        "provisional_full_shell_" + local_regime.removesuffix("_selected_output_carrier")
        if output_capture >= 0.90 else "full_shell_classification_withheld"
    )
    return {
        "regime": full_shell_regime,
        "selected_carrier_regime": local_regime,
        "output_carrier_sufficient_for_full_shell_classification": output_capture >= 0.90,
        "endpoint_output_modal_activity_capture": output_capture,
        "endpoint_m90_fraction": m90_fraction,
        "endpoint_shannon_support_fraction": effective_fraction,
        "temporal_support_regime": temporal_regime,
        "temporal_overlap_value": overlap_value,
        "temporal_overlap_authority": (
            "exact_top90" if top90_overlap is not None else
            "retained_top_set" if retained_overlap is not None else
            "unavailable"
        ),
        "interpretation": (
            "The selected carrier is broad, but a wider output carrier is required before assigning "
            "a full target-shell closure regime."
            if output_capture < 0.90 else
            "The selected outputs cover at least 90% of target-shell modal activity; the local regime "
            "is eligible for a full-shell provisional classification."
        ),
    }


def main() -> None:
    args = parse_args()
    payload = json.loads(args.receipt.read_text())
    endpoint = payload["endpoint_evolutions"][0]["endpoint"]
    snapshots = endpoint.get("interaction_closure_snapshots", [])
    summaries = [snapshot_summary(snapshot) for snapshot in snapshots]

    # Older receipts may predate in-run overlap telemetry.  Their retained
    # top sets still provide a clearly labelled, truncated overlap diagnostic.
    retained_overlap = []
    for previous, current in zip(snapshots, snapshots[1:]):
        left = {interaction_key(row) for row in previous.get("largest_interactions", [])}
        right = {interaction_key(row) for row in current.get("largest_interactions", [])}
        retained_overlap.append({
            "from_step": previous["step"],
            "to_step": current["step"],
            "retained_top_set_jaccard": jaccard(left, right),
            "warning": "overlap is for the retained top set, not J50/J90 unless those sets fit inside retention",
        })

    report = {
        "contract": "ns_interaction_closure_nonpromoting_report",
        "authority": {
            "empirical_non_promoting": True,
            "theorem_authority": False,
            "clay_authority": False,
        },
        "source_receipt": str(args.receipt),
        "endpoint": {
            "moving_packet_recurrence_ratio": endpoint["moving_packet_recurrence_ratio"],
            "moving_packet_heat_compensated_ratio": endpoint["moving_packet_heat_compensated_ratio"],
            "moving_packet_scale_displacement": endpoint["moving_packet_scale_displacement"],
        },
        "snapshots": summaries,
        "retained_set_overlap": retained_overlap,
        "classification": classify(summaries),
    }
    rendered = json.dumps(report, indent=2, sort_keys=True)
    if args.output_json:
        args.output_json.parent.mkdir(parents=True, exist_ok=True)
        args.output_json.write_text(rendered + "\n")
    print(rendered)


if __name__ == "__main__":
    main()
