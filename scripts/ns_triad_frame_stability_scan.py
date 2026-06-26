#!/usr/bin/env python3
"""Scan frame-stability and stratum-operator telemetry around the selected K_N carrier.

This producer is candidate-only and fail-closed. It reuses the raw N128 archive
and the local triad carrier conventions from the orbit/frustration scans, then
splits resonant triads into positive-backbone and negative-frame families,
builds finite operator proxies for each family, adds a stratum-aware
decomposition proxy from the selected mode shell radii, and mirrors the
cocycle-floor carrier summary when that companion scan is available.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Any

import numpy as np

from ns_boundary_pressure_gate_scan import _frame_indices, _pearson  # type: ignore
from ns_orbit_phase_coherence_scan import (  # type: ignore
    AUTHORITY,
    ModeRecord,
    _collect_modes,
    _frame_velocity,
    _json_text,
    _load_raw_bundle,
    _scalar_vorticity_spectrum,
)


SCRIPT_NAME = "scripts/ns_triad_frame_stability_scan.py"
CONTRACT = "ns_triad_frame_stability_scan"
ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_FRAME_STABILITY_SCAN"
SCHEMA_VERSION = "1.0.0"

OK_STATUS = "ok"
PARTIAL_STATUS = "partial"
ERROR_STATUS = "error"
ALLOWED_STATUSES = {OK_STATUS, PARTIAL_STATUS, ERROR_STATUS}

DEFAULT_RAW_ARCHIVE = Path(
    "/home/c/Documents/code/dashiCFD/outputs/"
    "sprint65_pressure_reconstruction_N128_seed0_gpu/ns3d_N128_seed0_gpu_pressure.npz"
)
DEFAULT_COCYCLE_FLOOR_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_cocycle_floor_scan_N128_20260621.json"
)
DEFAULT_OUTPUT_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_frame_stability_scan_N128_20260621.json"
)
DEFAULT_TOP_K = 48
DEFAULT_POOL_MULTIPLIER = 24
DEFAULT_ZERO_EPS = 1.0e-12
DEFAULT_TRIAD_SAMPLE_LIMIT = 8

CONTROL_CARD = {
    "O": "Measure candidate frame-stability telemetry around the selected K_N carrier.",
    "R": (
        "Build positive-backbone and negative-frame triad operator proxies from the selected "
        "mode carrier, mirror the cocycle-floor lower-bound input when present, then summarize "
        "frame-stability and stratum-aware decomposition signals."
    ),
    "C": SCRIPT_NAME,
    "S": "Telemetry only; the carrier, operator family, cocycle-floor mirror, and stratum proxy are empirical and non-promoting.",
    "L": (
        "Load raw frames, select dominant Fourier-vorticity modes, form resonant triads, "
        "split them into positive-backbone and negative-frame families, import the cocycle-floor "
        "carrier summary, and emit operator telemetry."
    ),
    "P": ROUTE_DECISION,
    "G": "No theorem, Clay, or route promotion is inferred from this scan.",
    "F": "This script records finite operator proxies and mirrored lower-bound inputs only; it does not prove any stability or decomposition claim.",
}


@dataclass(frozen=True)
class TriadRecord:
    left: int
    right: int
    out: int
    weight: float
    closure: float
    coherence: float
    shell_spread: float
    distinct_strata: int
    stratum_profile: tuple[int, int, int]


def _coerce_int(value: Any) -> int | None:
    if value is None or isinstance(value, bool):
        return None
    if isinstance(value, int):
        return int(value)
    if isinstance(value, float) and math.isfinite(value) and value.is_integer():
        return int(value)
    return None


def _coerce_float(value: Any) -> float | None:
    if value is None or isinstance(value, bool):
        return None
    try:
        parsed = float(value)
    except (TypeError, ValueError):
        return None
    return parsed if math.isfinite(parsed) else None


def _load_json(path: Path) -> dict[str, Any] | None:
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError:
        return None
    if not isinstance(payload, dict):
        return None
    return payload


def _rows(payload: dict[str, Any] | None) -> list[dict[str, Any]]:
    if not isinstance(payload, dict):
        return []
    for key in ("rows", "triad_frame_stability_rows"):
        value = payload.get(key)
        if isinstance(value, list):
            return [row for row in value if isinstance(row, dict)]
    return []


def _select_cocycle_floor_carrier(payload: dict[str, Any] | None) -> dict[int, dict[str, Any]]:
    selected: dict[int, dict[str, Any]] = {}
    for row in _rows(payload):
        frame = _coerce_int(row.get("frame"))
        if frame is None:
            continue
        candidate = {
            "frame": int(frame),
            "shell": _coerce_int(row.get("shell")),
            "reference_id": row.get("best_reference_id"),
            "reference_kind": row.get("best_reference_kind"),
            "floor_proxy": _coerce_float(row.get("best_reference_floor_proxy")),
            "floor_ratio_vs_raw": _coerce_float(row.get("frustration_floor_ratio_vs_raw")),
            "lambda_max_proxy": _coerce_float(row.get("best_reference_lambda_max_proxy")),
            "mean_cycle_lower_bound": _coerce_float(row.get("mean_cycle_lower_bound")),
            "mean_cycle_lower_bound_normalized": _coerce_float(row.get("cycle_lower_bound_normalized_mean")),
        }
        existing = selected.get(int(frame))
        if existing is None:
            selected[int(frame)] = candidate
            continue
        existing_floor = existing.get("floor_proxy")
        candidate_floor = candidate.get("floor_proxy")
        existing_lambda = existing.get("lambda_max_proxy")
        candidate_lambda = candidate.get("lambda_max_proxy")
        better = False
        if candidate_floor is not None and existing_floor is not None:
            better = candidate_floor < existing_floor or (
                candidate_floor == existing_floor
                and candidate_lambda is not None
                and (existing_lambda is None or candidate_lambda > existing_lambda)
            )
        elif candidate_floor is not None and existing_floor is None:
            better = True
        if better:
            selected[int(frame)] = candidate
    return selected


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--raw-archive", type=Path, default=DEFAULT_RAW_ARCHIVE)
    parser.add_argument("--cocycle-floor-json", type=Path, default=DEFAULT_COCYCLE_FLOOR_JSON)
    parser.add_argument("--output-json", type=Path, default=DEFAULT_OUTPUT_JSON)
    parser.add_argument("--frame", type=int, default=None)
    parser.add_argument("--frame-limit", type=int, default=None)
    parser.add_argument("--top-k", type=int, default=DEFAULT_TOP_K)
    parser.add_argument("--pool-multiplier", type=int, default=DEFAULT_POOL_MULTIPLIER)
    parser.add_argument("--zero-eps", type=float, default=DEFAULT_ZERO_EPS)
    parser.add_argument("--triad-sample-limit", type=int, default=DEFAULT_TRIAD_SAMPLE_LIMIT)
    parser.add_argument("--pretty", action="store_true")
    return parser.parse_args()


def _fraction(numerator: float, denominator: float) -> float:
    if denominator <= 0.0:
        return 0.0
    return float(numerator) / float(denominator)


def _json_text(payload: dict[str, Any], pretty: bool) -> str:
    if pretty:
        return json.dumps(payload, sort_keys=True, indent=2, ensure_ascii=False, allow_nan=False)
    return json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=False, allow_nan=False)


def _wrap_phase(angle: float) -> float:
    wrapped = (float(angle) + math.pi) % (2.0 * math.pi) - math.pi
    if wrapped <= -math.pi:
        wrapped += 2.0 * math.pi
    return float(wrapped)


def _weighted_quantile(values: np.ndarray, weights: np.ndarray, quantile: float) -> float:
    if len(values) == 0:
        return 0.0
    q = min(max(float(quantile), 0.0), 1.0)
    order = np.argsort(values)
    sorted_values = np.asarray(values[order], dtype=np.float64)
    sorted_weights = np.asarray(weights[order], dtype=np.float64)
    total = float(np.sum(sorted_weights))
    if total <= 0.0 or not math.isfinite(total):
        return float(sorted_values[-1])
    cutoff = q * total
    cumulative = np.cumsum(sorted_weights)
    index = int(np.searchsorted(cumulative, cutoff, side="left"))
    index = max(0, min(index, len(sorted_values) - 1))
    return float(sorted_values[index])


def _normalized_entropy(weights: np.ndarray) -> float:
    if len(weights) == 0:
        return 0.0
    total = float(np.sum(weights))
    if total <= 0.0 or not math.isfinite(total):
        return 0.0
    normalized = np.asarray(weights, dtype=np.float64) / total
    active = normalized[normalized > 0.0]
    if len(active) <= 1:
        return 0.0
    entropy = float(-np.sum(active * np.log(active)))
    return entropy / math.log(float(len(normalized)))


def _laplacian_from_adjacency(adjacency: np.ndarray, signed: bool) -> np.ndarray:
    if adjacency.size == 0:
        return np.zeros_like(adjacency, dtype=np.float64)
    if signed:
        degree = np.sum(np.abs(adjacency), axis=1)
    else:
        degree = np.sum(adjacency, axis=1)
    return np.diag(degree) - adjacency


def _smallest_positive_eigenvalue(eigenvalues: np.ndarray, tol: float) -> float:
    positives = np.asarray([float(value) for value in eigenvalues if float(value) > float(tol)], dtype=np.float64)
    if len(positives) == 0:
        return 0.0
    return float(np.min(positives))


def _mode_strata(shell_radii: np.ndarray) -> tuple[np.ndarray, int, list[float]]:
    if len(shell_radii) == 0:
        return np.zeros(0, dtype=np.int64), 0, []
    unique_shells = np.unique(np.asarray(shell_radii, dtype=np.float64))
    if len(unique_shells) <= 1:
        return np.zeros(len(shell_radii), dtype=np.int64), 1, []
    bins = min(3, int(len(unique_shells)))
    if bins <= 1:
        return np.zeros(len(shell_radii), dtype=np.int64), 1, []
    quantiles = [i / float(bins) for i in range(1, bins)]
    thresholds = [float(np.quantile(shell_radii, q)) for q in quantiles]
    raw_labels = np.digitize(shell_radii, thresholds, right=True)
    unique_labels = sorted(int(value) for value in np.unique(raw_labels))
    remap = {label: idx for idx, label in enumerate(unique_labels)}
    labels = np.asarray([remap[int(value)] for value in raw_labels], dtype=np.int64)
    return labels, len(unique_labels), thresholds


def _family_laplacians(
    triads: list[TriadRecord],
    mode_count: int,
) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    positive = np.zeros((mode_count, mode_count), dtype=np.float64)
    negative = np.zeros_like(positive)
    combined = np.zeros_like(positive)

    for triad in triads:
        pair_weight = float(triad.weight) / 3.0
        positive_weight = pair_weight * max(float(triad.coherence), 0.0)
        negative_weight = pair_weight * max(-float(triad.coherence), 0.0)
        signed_weight = pair_weight * float(triad.coherence)
        for left, right in ((triad.left, triad.right), (triad.left, triad.out), (triad.right, triad.out)):
            positive[left, right] += positive_weight
            positive[right, left] += positive_weight
            negative[left, right] += negative_weight
            negative[right, left] += negative_weight
            combined[left, right] += signed_weight
            combined[right, left] += signed_weight

    return positive, negative, combined


def _operator_metrics(adjacency: np.ndarray, *, signed: bool, zero_eps: float) -> dict[str, Any]:
    if adjacency.size == 0:
        return {
            "trace": 0.0,
            "spectral_gap_proxy": 0.0,
            "zero_eigen_count": 0,
        }
    laplacian = _laplacian_from_adjacency(adjacency, signed=signed)
    eigenvalues = np.linalg.eigvalsh(laplacian) if laplacian.shape[0] > 1 else np.asarray([float(laplacian[0, 0])], dtype=np.float64)
    tol = max(float(DEFAULT_ZERO_EPS), float(zero_eps) * 100.0)
    return {
        "trace": float(np.trace(laplacian)),
        "spectral_gap_proxy": float(_smallest_positive_eigenvalue(eigenvalues, tol)),
        "zero_eigen_count": int(np.sum(np.abs(eigenvalues) <= tol)),
    }


def _build_frame_surface(
    modes: list[ModeRecord],
    zero_eps: float,
    triad_sample_limit: int,
) -> tuple[list[TriadRecord], dict[str, Any]]:
    if len(modes) < 3:
        amplitudes = np.asarray([mode.amplitude for mode in modes], dtype=np.float64)
        amp_sum = float(np.sum(amplitudes))
        mode_concentration = _fraction(float(np.max(amplitudes)) if len(amplitudes) else 0.0, amp_sum)
        return [], {
            "selected_mode_count": len(modes),
            "selected_mode_amplitude_sum": amp_sum,
            "mode_concentration_fraction": mode_concentration,
            "carrier_shell_radius_mean": float(np.mean([mode.shell_radius for mode in modes])) if modes else 0.0,
            "carrier_shell_radius_p95": float(np.max([mode.shell_radius for mode in modes])) if modes else 0.0,
            "carrier_stratum_count": len(modes),
            "carrier_stratum_thresholds": [],
            "triad_count": 0,
            "triad_weight_sum": 0.0,
            "triad_weight_mean": 0.0,
            "triad_weight_p95": 0.0,
            "triad_shell_spread_mean": 0.0,
            "triad_shell_spread_p95": 0.0,
            "triad_phase_coherence_mean": 0.0,
            "triad_phase_coherence_abs_mean": 0.0,
            "triad_positive_backbone_count": 0,
            "triad_negative_frame_count": 0,
            "triad_positive_backbone_mass": 0.0,
            "triad_negative_frame_mass": 0.0,
            "triad_positive_backbone_mass_ratio": 0.0,
            "triad_negative_frame_mass_ratio": 0.0,
            "positive_backbone_operator_trace": 0.0,
            "positive_backbone_operator_gap_proxy": 0.0,
            "positive_backbone_operator_zero_eigen_count": 0,
            "negative_frame_operator_trace": 0.0,
            "negative_frame_operator_gap_proxy": 0.0,
            "negative_frame_operator_zero_eigen_count": 0,
            "combined_operator_trace": 0.0,
            "combined_operator_gap_proxy": 0.0,
            "combined_operator_zero_eigen_count": 0,
            "frame_stability_proxy": 0.0,
            "frame_stability_margin_proxy": 0.0,
            "backbone_vs_negative_gap_ratio": 0.0,
            "stratum_internal_mass_ratio": 0.0,
            "stratum_cross_mass_ratio": 0.0,
            "stratum_balance_entropy_normalized": 0.0,
            "triad_profile_entropy_normalized": 0.0,
            "stratum_decomposition_proxy": 0.0,
            "stratum_records": [],
            "triad_samples": [],
        }

    key_to_index = {mode.key: idx for idx, mode in enumerate(modes)}
    amplitudes = np.asarray([mode.amplitude for mode in modes], dtype=np.float64)
    shell_radii = np.asarray([mode.shell_radius for mode in modes], dtype=np.float64)
    stratum_labels, stratum_count, thresholds = _mode_strata(shell_radii)
    amp_sum = float(np.sum(amplitudes))
    mode_concentration = _fraction(float(np.max(amplitudes)), amp_sum)
    carrier_shell_radius_mean = float(np.mean(shell_radii))
    carrier_shell_radius_p95 = float(_weighted_quantile(shell_radii, amplitudes, 0.95))
    stratum_mode_counts = np.bincount(stratum_labels, minlength=max(1, stratum_count)).astype(np.float64)
    stratum_amp_sum = np.bincount(stratum_labels, weights=amplitudes, minlength=max(1, stratum_count)).astype(np.float64)
    stratum_mode_entropy = _normalized_entropy(stratum_amp_sum)

    triads: list[TriadRecord] = []
    positive_backbone_mass = 0.0
    negative_frame_mass = 0.0
    triad_weight_sum = 0.0
    triad_weight_values: list[float] = []
    phase_coherence_weighted = 0.0
    phase_coherence_abs_weighted = 0.0
    shell_spreads: list[float] = []
    triad_stratum_mass = np.zeros(max(1, stratum_count), dtype=np.float64)
    triad_backbone_mass = np.zeros(max(1, stratum_count), dtype=np.float64)
    triad_negative_mass = np.zeros(max(1, stratum_count), dtype=np.float64)
    profile_weights: dict[tuple[int, int, int], float] = {}
    internal_mass = 0.0
    cross_mass = 0.0

    for left in range(len(modes)):
        mode_left = modes[left]
        for right in range(left + 1, len(modes)):
            mode_right = modes[right]
            key_out = (
                mode_left.key[0] + mode_right.key[0],
                mode_left.key[1] + mode_right.key[1],
                mode_left.key[2] + mode_right.key[2],
            )
            out = key_to_index.get(key_out)
            if out is None or out == left or out == right:
                continue
            mode_out = modes[out]
            weight = mode_left.amplitude * mode_right.amplitude * mode_out.amplitude
            if not math.isfinite(weight) or weight <= float(zero_eps):
                continue

            closure = _wrap_phase(mode_left.phase + mode_right.phase - mode_out.phase)
            coherence = float(math.cos(closure))
            distinct_strata = len({int(stratum_labels[left]), int(stratum_labels[right]), int(stratum_labels[out])})
            stratum_profile = tuple(
                sorted((int(stratum_labels[left]), int(stratum_labels[right]), int(stratum_labels[out])))
            )
            shell_spread = max(mode_left.shell_radius, mode_right.shell_radius, mode_out.shell_radius) - min(
                mode_left.shell_radius,
                mode_right.shell_radius,
                mode_out.shell_radius,
            )
            triads.append(
                TriadRecord(
                    left=int(left),
                    right=int(right),
                    out=int(out),
                    weight=float(weight),
                    closure=float(closure),
                    coherence=float(coherence),
                    shell_spread=float(shell_spread),
                    distinct_strata=int(distinct_strata),
                    stratum_profile=stratum_profile,
                )
            )

            triad_weight_sum += float(weight)
            triad_weight_values.append(float(weight))
            phase_coherence_weighted += float(weight) * coherence
            phase_coherence_abs_weighted += float(weight) * abs(coherence)
            shell_spreads.append(float(shell_spread))
            if coherence >= 0.0:
                positive_backbone_mass += float(weight) * coherence
            else:
                negative_frame_mass += float(weight) * (-coherence)

            if distinct_strata == 1:
                internal_mass += float(weight)
            else:
                cross_mass += float(weight)
            profile_weights[stratum_profile] = profile_weights.get(stratum_profile, 0.0) + float(weight)

            share = float(weight) / 3.0
            for idx in (left, right, out):
                stratum = int(stratum_labels[idx])
                triad_stratum_mass[stratum] += share
                if coherence >= 0.0:
                    triad_backbone_mass[stratum] += share * coherence
                else:
                    triad_negative_mass[stratum] += share * (-coherence)

    triad_count = len(triads)
    if triad_count == 0 or triad_weight_sum <= float(zero_eps):
        return triads, {
            "selected_mode_count": len(modes),
            "selected_mode_amplitude_sum": amp_sum,
            "mode_concentration_fraction": mode_concentration,
            "carrier_shell_radius_mean": carrier_shell_radius_mean,
            "carrier_shell_radius_p95": carrier_shell_radius_p95,
            "carrier_stratum_count": int(stratum_count),
            "carrier_stratum_thresholds": [float(value) for value in thresholds],
            "triad_count": 0,
            "triad_weight_sum": 0.0,
            "triad_weight_mean": 0.0,
            "triad_weight_p95": 0.0,
            "triad_shell_spread_mean": 0.0,
            "triad_shell_spread_p95": 0.0,
            "triad_phase_coherence_mean": 0.0,
            "triad_phase_coherence_abs_mean": 0.0,
            "triad_positive_backbone_count": 0,
            "triad_negative_frame_count": 0,
            "triad_positive_backbone_mass": 0.0,
            "triad_negative_frame_mass": 0.0,
            "triad_positive_backbone_mass_ratio": 0.0,
            "triad_negative_frame_mass_ratio": 0.0,
            "positive_backbone_operator_trace": 0.0,
            "positive_backbone_operator_gap_proxy": 0.0,
            "positive_backbone_operator_zero_eigen_count": 0,
            "negative_frame_operator_trace": 0.0,
            "negative_frame_operator_gap_proxy": 0.0,
            "negative_frame_operator_zero_eigen_count": 0,
            "combined_operator_trace": 0.0,
            "combined_operator_gap_proxy": 0.0,
            "combined_operator_zero_eigen_count": 0,
            "frame_stability_proxy": 0.0,
            "frame_stability_margin_proxy": 0.0,
            "backbone_vs_negative_gap_ratio": 0.0,
            "stratum_internal_mass_ratio": _fraction(internal_mass, triad_weight_sum),
            "stratum_cross_mass_ratio": _fraction(cross_mass, triad_weight_sum),
            "stratum_balance_entropy_normalized": float(stratum_mode_entropy),
            "triad_profile_entropy_normalized": 0.0,
            "stratum_decomposition_proxy": 0.0,
            "stratum_records": [],
            "triad_samples": [],
        }

    triads_sorted = sorted(triads, key=lambda triad: (float(triad.weight) * abs(float(triad.coherence)), float(triad.weight)), reverse=True)
    positive_triads = [triad for triad in triads if float(triad.coherence) >= 0.0]
    negative_triads = [triad for triad in triads if float(triad.coherence) < 0.0]

    positive_adj, negative_adj, combined_adj = _family_laplacians(triads, len(modes))
    positive_operator = _operator_metrics(positive_adj, signed=False, zero_eps=zero_eps)
    negative_operator = _operator_metrics(negative_adj, signed=False, zero_eps=zero_eps)
    combined_operator = _operator_metrics(combined_adj, signed=True, zero_eps=zero_eps)

    positive_mass_ratio = _fraction(positive_backbone_mass, triad_weight_sum)
    negative_mass_ratio = _fraction(negative_frame_mass, triad_weight_sum)
    phase_coherence_mean = _fraction(phase_coherence_weighted, triad_weight_sum)
    phase_coherence_abs_mean = _fraction(phase_coherence_abs_weighted, triad_weight_sum)
    triad_weight_mean = float(np.mean(np.asarray(triad_weight_values, dtype=np.float64)))
    triad_weight_p95 = _weighted_quantile(
        np.asarray(triad_weight_values, dtype=np.float64),
        np.asarray(triad_weight_values, dtype=np.float64),
        0.95,
    )
    shell_spread_mean = _fraction(float(np.sum(np.asarray(triad_weight_values, dtype=np.float64) * np.asarray(shell_spreads, dtype=np.float64))), triad_weight_sum)
    shell_spread_p95 = _weighted_quantile(np.asarray(shell_spreads, dtype=np.float64), np.asarray(triad_weight_values, dtype=np.float64), 0.95)
    positive_gap = float(positive_operator["spectral_gap_proxy"])
    negative_gap = float(negative_operator["spectral_gap_proxy"])
    combined_gap = float(combined_operator["spectral_gap_proxy"])
    backbone_vs_negative_gap_ratio = _fraction(positive_gap, negative_gap + float(zero_eps))
    frame_stability_proxy = max(0.0, _fraction(positive_gap, 1.0 + float(negative_operator["trace"])) * max(0.0, 1.0 - negative_mass_ratio))
    frame_stability_margin_proxy = max(0.0, positive_mass_ratio - negative_mass_ratio)

    profile_distribution = np.asarray(list(profile_weights.values()), dtype=np.float64)
    triad_profile_entropy = _normalized_entropy(profile_distribution)
    stratum_internal_mass_ratio = _fraction(internal_mass, triad_weight_sum)
    stratum_cross_mass_ratio = _fraction(cross_mass, triad_weight_sum)
    stratum_decomposition_proxy = float(
        stratum_cross_mass_ratio * 0.5 * (triad_profile_entropy + float(stratum_mode_entropy))
    )

    stratum_records: list[dict[str, Any]] = []
    for stratum in range(int(stratum_count)):
        stratum_records.append(
            {
                "stratum_index": int(stratum),
                "mode_count": int(stratum_mode_counts[stratum]),
                "mode_amplitude_sum": float(stratum_amp_sum[stratum]),
                "mode_mass_fraction": _fraction(float(stratum_amp_sum[stratum]), amp_sum),
                "triad_mass_fraction": _fraction(float(triad_stratum_mass[stratum]), triad_weight_sum),
                "backbone_mass_fraction": _fraction(float(triad_backbone_mass[stratum]), triad_weight_sum),
                "negative_frame_mass_fraction": _fraction(float(triad_negative_mass[stratum]), triad_weight_sum),
            }
        )

    sample_limit = max(0, int(triad_sample_limit))
    triad_samples = [
        {
            "left": int(triad.left),
            "right": int(triad.right),
            "out": int(triad.out),
            "weight": float(triad.weight),
            "closure": float(triad.closure),
            "coherence": float(triad.coherence),
            "family": "positive_backbone" if float(triad.coherence) >= 0.0 else "negative_frame",
            "shell_spread": float(triad.shell_spread),
            "distinct_strata": int(triad.distinct_strata),
            "stratum_profile": list(triad.stratum_profile),
        }
        for triad in triads_sorted[:sample_limit]
    ]

    return triads, {
        "selected_mode_count": len(modes),
        "selected_mode_amplitude_sum": float(amp_sum),
        "mode_concentration_fraction": float(mode_concentration),
        "carrier_shell_radius_mean": float(carrier_shell_radius_mean),
        "carrier_shell_radius_p95": float(carrier_shell_radius_p95),
        "carrier_stratum_count": int(stratum_count),
        "carrier_stratum_thresholds": [float(value) for value in thresholds],
        "triad_count": int(triad_count),
        "triad_weight_sum": float(triad_weight_sum),
        "triad_weight_mean": float(triad_weight_mean),
        "triad_weight_p95": float(triad_weight_p95),
        "triad_shell_spread_mean": float(shell_spread_mean),
        "triad_shell_spread_p95": float(shell_spread_p95),
        "triad_phase_coherence_mean": float(phase_coherence_mean),
        "triad_phase_coherence_abs_mean": float(phase_coherence_abs_mean),
        "triad_positive_backbone_count": int(len(positive_triads)),
        "triad_negative_frame_count": int(len(negative_triads)),
        "triad_positive_backbone_mass": float(positive_backbone_mass),
        "triad_negative_frame_mass": float(negative_frame_mass),
        "triad_positive_backbone_mass_ratio": float(positive_mass_ratio),
        "triad_negative_frame_mass_ratio": float(negative_mass_ratio),
        "positive_backbone_operator_trace": float(positive_operator["trace"]),
        "positive_backbone_operator_gap_proxy": float(positive_gap),
        "positive_backbone_operator_zero_eigen_count": int(positive_operator["zero_eigen_count"]),
        "negative_frame_operator_trace": float(negative_operator["trace"]),
        "negative_frame_operator_gap_proxy": float(negative_gap),
        "negative_frame_operator_zero_eigen_count": int(negative_operator["zero_eigen_count"]),
        "combined_operator_trace": float(combined_operator["trace"]),
        "combined_operator_gap_proxy": float(combined_gap),
        "combined_operator_zero_eigen_count": int(combined_operator["zero_eigen_count"]),
        "frame_stability_proxy": float(frame_stability_proxy),
        "frame_stability_margin_proxy": float(frame_stability_margin_proxy),
        "backbone_vs_negative_gap_ratio": float(backbone_vs_negative_gap_ratio),
        "stratum_internal_mass_ratio": float(stratum_internal_mass_ratio),
        "stratum_cross_mass_ratio": float(stratum_cross_mass_ratio),
        "stratum_balance_entropy_normalized": float(stratum_mode_entropy),
        "triad_profile_entropy_normalized": float(triad_profile_entropy),
        "stratum_decomposition_proxy": float(stratum_decomposition_proxy),
        "stratum_records": stratum_records,
        "triad_samples": triad_samples,
    }


def _evaluate_frame(
    slot: int,
    snapshot: int,
    bundle: Any,
    cocycle_floor_record: dict[str, Any] | None,
    top_k: int,
    pool_multiplier: int,
    zero_eps: float,
    triad_sample_limit: int,
) -> tuple[str, dict[str, Any]]:
    row: dict[str, Any] = {
        "frame": int(slot),
        "snapshot_index": int(snapshot),
        "source": str(bundle.path),
        "orbit_phase": float(snapshot),
        "top_k": int(top_k),
        "pool_multiplier": int(pool_multiplier),
        "zero_eps": float(zero_eps),
        "triad_sample_limit": int(triad_sample_limit),
        "cocycle_floor_input_available": bool(cocycle_floor_record is not None),
        "operator_family": "K_N",
        "route_mode": "fail-closed",
        "fail_closed": True,
        "candidate_only": True,
        "empirical_non_promoting": True,
    }
    try:
        u, v, w = _frame_velocity(bundle, snapshot)
        spectrum = _scalar_vorticity_spectrum(u, v, w, bundle.domain_length)
        modes = _collect_modes(
            spectrum,
            top_k=int(top_k),
            zero_eps=float(zero_eps),
            pool_multiplier=int(pool_multiplier),
        )
        _triads, metrics = _build_frame_surface(modes, zero_eps=zero_eps, triad_sample_limit=triad_sample_limit)
    except Exception as exc:  # noqa: BLE001
        row["status"] = ERROR_STATUS
        row["errors"] = [f"frame_triad_frame_stability_scan_error: {exc}"]
        return ERROR_STATUS, row

    row.update(
        {
            "selected_mode_count": int(metrics["selected_mode_count"]),
            "selected_mode_amplitude_sum": float(metrics["selected_mode_amplitude_sum"]),
            "mode_concentration_fraction": float(metrics["mode_concentration_fraction"]),
            "carrier_shell_radius_mean": float(metrics["carrier_shell_radius_mean"]),
            "carrier_shell_radius_p95": float(metrics["carrier_shell_radius_p95"]),
            "carrier_stratum_count": int(metrics["carrier_stratum_count"]),
            "carrier_stratum_thresholds": list(metrics["carrier_stratum_thresholds"]),
            "triad_count": int(metrics["triad_count"]),
            "triad_weight_sum": float(metrics["triad_weight_sum"]),
            "triad_weight_mean": float(metrics["triad_weight_mean"]),
            "triad_weight_p95": float(metrics["triad_weight_p95"]),
            "triad_shell_spread_mean": float(metrics["triad_shell_spread_mean"]),
            "triad_shell_spread_p95": float(metrics["triad_shell_spread_p95"]),
            "triad_phase_coherence_mean": float(metrics["triad_phase_coherence_mean"]),
            "triad_phase_coherence_abs_mean": float(metrics["triad_phase_coherence_abs_mean"]),
            "triad_positive_backbone_count": int(metrics["triad_positive_backbone_count"]),
            "triad_negative_frame_count": int(metrics["triad_negative_frame_count"]),
            "triad_positive_backbone_mass": float(metrics["triad_positive_backbone_mass"]),
            "triad_negative_frame_mass": float(metrics["triad_negative_frame_mass"]),
            "triad_positive_backbone_mass_ratio": float(metrics["triad_positive_backbone_mass_ratio"]),
            "triad_negative_frame_mass_ratio": float(metrics["triad_negative_frame_mass_ratio"]),
            "positive_backbone_operator_trace": float(metrics["positive_backbone_operator_trace"]),
            "positive_backbone_operator_gap_proxy": float(metrics["positive_backbone_operator_gap_proxy"]),
            "positive_backbone_operator_zero_eigen_count": int(metrics["positive_backbone_operator_zero_eigen_count"]),
            "negative_frame_operator_trace": float(metrics["negative_frame_operator_trace"]),
            "negative_frame_operator_gap_proxy": float(metrics["negative_frame_operator_gap_proxy"]),
            "negative_frame_operator_zero_eigen_count": int(metrics["negative_frame_operator_zero_eigen_count"]),
            "combined_operator_trace": float(metrics["combined_operator_trace"]),
            "combined_operator_gap_proxy": float(metrics["combined_operator_gap_proxy"]),
            "combined_operator_zero_eigen_count": int(metrics["combined_operator_zero_eigen_count"]),
            "frame_stability_proxy": float(metrics["frame_stability_proxy"]),
            "frame_stability_margin_proxy": float(metrics["frame_stability_margin_proxy"]),
            "backbone_vs_negative_gap_ratio": float(metrics["backbone_vs_negative_gap_ratio"]),
            "stratum_internal_mass_ratio": float(metrics["stratum_internal_mass_ratio"]),
            "stratum_cross_mass_ratio": float(metrics["stratum_cross_mass_ratio"]),
            "stratum_balance_entropy_normalized": float(metrics["stratum_balance_entropy_normalized"]),
            "triad_profile_entropy_normalized": float(metrics["triad_profile_entropy_normalized"]),
            "stratum_decomposition_proxy": float(metrics["stratum_decomposition_proxy"]),
            "cocycle_floor_input_available": bool(cocycle_floor_record is not None),
            "cocycle_floor_selected_shell": int(cocycle_floor_record["shell"]) if cocycle_floor_record and cocycle_floor_record.get("shell") is not None else None,
            "cocycle_floor_selected_reference_id": cocycle_floor_record.get("reference_id") if cocycle_floor_record else None,
            "cocycle_floor_selected_reference_kind": cocycle_floor_record.get("reference_kind") if cocycle_floor_record else None,
            "cocycle_floor_selected_floor_proxy": float(cocycle_floor_record["floor_proxy"]) if cocycle_floor_record and cocycle_floor_record.get("floor_proxy") is not None else None,
            "cocycle_floor_selected_floor_ratio_vs_raw": float(cocycle_floor_record["floor_ratio_vs_raw"]) if cocycle_floor_record and cocycle_floor_record.get("floor_ratio_vs_raw") is not None else None,
            "cocycle_floor_selected_lambda_max_proxy": float(cocycle_floor_record["lambda_max_proxy"]) if cocycle_floor_record and cocycle_floor_record.get("lambda_max_proxy") is not None else None,
            "cocycle_floor_selected_mean_cycle_lower_bound": float(cocycle_floor_record["mean_cycle_lower_bound"]) if cocycle_floor_record and cocycle_floor_record.get("mean_cycle_lower_bound") is not None else None,
            "cocycle_floor_selected_mean_cycle_lower_bound_normalized": float(cocycle_floor_record["mean_cycle_lower_bound_normalized"]) if cocycle_floor_record and cocycle_floor_record.get("mean_cycle_lower_bound_normalized") is not None else None,
            "stratum_records": list(metrics["stratum_records"]),
            "triad_samples": list(metrics["triad_samples"]),
        }
    )

    warnings: list[str] = []
    if int(metrics["triad_count"]) <= 0:
        warnings.append("no resonant selected-mode triads found")
    if float(metrics["positive_backbone_operator_gap_proxy"]) <= 0.0:
        warnings.append("positive-backbone operator has no positive spectral-gap proxy")
    if float(metrics["negative_frame_operator_gap_proxy"]) <= 0.0:
        warnings.append("negative-frame operator has no positive spectral-gap proxy")
    if float(metrics["carrier_stratum_count"]) <= 1:
        warnings.append("stratum-aware decomposition collapsed to a single stratum")
    if cocycle_floor_record is None:
        warnings.append("no matching cocycle-floor carrier summary found for this frame")
    if warnings:
        row["status"] = PARTIAL_STATUS
        row["warnings"] = warnings
        return PARTIAL_STATUS, row

    row["status"] = OK_STATUS
    return OK_STATUS, row


def _aggregate_rows(rows: list[dict[str, Any]]) -> dict[str, Any]:
    ok_rows = [row for row in rows if row.get("status") == OK_STATUS]

    def _series(key: str) -> list[float]:
        values: list[float] = []
        for row in ok_rows:
            value = row.get(key)
            if isinstance(value, (int, float)) and math.isfinite(float(value)):
                values.append(float(value))
        return values

    series_selected_mode_count = _series("selected_mode_count")
    series_triad_count = _series("triad_count")
    series_triad_weight_sum = _series("triad_weight_sum")
    series_phase_coherence = _series("triad_phase_coherence_mean")
    series_negative_ratio = _series("triad_negative_frame_mass_ratio")
    series_positive_gap = _series("positive_backbone_operator_gap_proxy")
    series_negative_gap = _series("negative_frame_operator_gap_proxy")
    series_combined_gap = _series("combined_operator_gap_proxy")
    series_frame_stability = _series("frame_stability_proxy")
    series_frame_margin = _series("frame_stability_margin_proxy")
    series_stratum_internal = _series("stratum_internal_mass_ratio")
    series_stratum_cross = _series("stratum_cross_mass_ratio")
    series_stratum_decomposition = _series("stratum_decomposition_proxy")
    series_gap_ratio = _series("backbone_vs_negative_gap_ratio")
    series_shell_mean = _series("triad_shell_spread_mean")
    series_shell_p95 = _series("triad_shell_spread_p95")
    series_cocycle_floor = _series("cocycle_floor_selected_floor_proxy")
    series_cocycle_floor_ratio = _series("cocycle_floor_selected_floor_ratio_vs_raw")
    series_cocycle_lambda_max = _series("cocycle_floor_selected_lambda_max_proxy")
    series_cocycle_cycle_lower_bound = _series("cocycle_floor_selected_mean_cycle_lower_bound")
    series_cocycle_cycle_lower_bound_normalized = _series("cocycle_floor_selected_mean_cycle_lower_bound_normalized")

    return {
        "processed_frames": len(rows),
        "ok_frames": sum(1 for row in rows if row.get("status") == OK_STATUS),
        "partial_frames": sum(1 for row in rows if row.get("status") == PARTIAL_STATUS),
        "error_frames": sum(1 for row in rows if row.get("status") == ERROR_STATUS),
        "top_k": int(ok_rows[0]["top_k"]) if ok_rows else None,
        "pool_multiplier": int(ok_rows[0]["pool_multiplier"]) if ok_rows else None,
        "zero_eps": float(ok_rows[0].get("zero_eps", DEFAULT_ZERO_EPS)) if ok_rows else float(DEFAULT_ZERO_EPS),
        "triad_sample_limit": int(ok_rows[0]["triad_sample_limit"]) if ok_rows else int(DEFAULT_TRIAD_SAMPLE_LIMIT),
        "triad_count_total": int(sum(int(row.get("triad_count", 0)) for row in ok_rows)),
        "selected_mode_count_mean": float(np.mean(series_selected_mode_count)) if series_selected_mode_count else 0.0,
        "triad_count_mean": float(np.mean(series_triad_count)) if series_triad_count else 0.0,
        "triad_weight_sum_mean": float(np.mean(series_triad_weight_sum)) if series_triad_weight_sum else 0.0,
        "triad_phase_coherence_mean": float(np.mean(series_phase_coherence)) if series_phase_coherence else 0.0,
        "triad_positive_backbone_mass_ratio_mean": float(np.mean(_series("triad_positive_backbone_mass_ratio"))) if _series("triad_positive_backbone_mass_ratio") else 0.0,
        "triad_negative_frame_mass_ratio_mean": float(np.mean(series_negative_ratio)) if series_negative_ratio else 0.0,
        "positive_backbone_operator_gap_proxy_mean": float(np.mean(series_positive_gap)) if series_positive_gap else 0.0,
        "negative_frame_operator_gap_proxy_mean": float(np.mean(series_negative_gap)) if series_negative_gap else 0.0,
        "combined_operator_gap_proxy_mean": float(np.mean(series_combined_gap)) if series_combined_gap else 0.0,
        "frame_stability_proxy_mean": float(np.mean(series_frame_stability)) if series_frame_stability else 0.0,
        "frame_stability_margin_proxy_mean": float(np.mean(series_frame_margin)) if series_frame_margin else 0.0,
        "stratum_internal_mass_ratio_mean": float(np.mean(series_stratum_internal)) if series_stratum_internal else 0.0,
        "stratum_cross_mass_ratio_mean": float(np.mean(series_stratum_cross)) if series_stratum_cross else 0.0,
        "stratum_decomposition_proxy_mean": float(np.mean(series_stratum_decomposition)) if series_stratum_decomposition else 0.0,
        "positive_backbone_vs_negative_frame_gap_ratio_mean": float(np.mean(series_gap_ratio)) if series_gap_ratio else 0.0,
        "triad_shell_spread_mean": float(np.mean(series_shell_mean)) if series_shell_mean else 0.0,
        "triad_shell_spread_p95_mean": float(np.mean(series_shell_p95)) if series_shell_p95 else 0.0,
        "cocycle_floor_selected_floor_proxy_mean": float(np.mean(series_cocycle_floor)) if series_cocycle_floor else 0.0,
        "cocycle_floor_selected_floor_ratio_vs_raw_mean": float(np.mean(series_cocycle_floor_ratio)) if series_cocycle_floor_ratio else 0.0,
        "cocycle_floor_selected_lambda_max_proxy_mean": float(np.mean(series_cocycle_lambda_max)) if series_cocycle_lambda_max else 0.0,
        "cocycle_floor_selected_mean_cycle_lower_bound_mean": float(np.mean(series_cocycle_cycle_lower_bound)) if series_cocycle_cycle_lower_bound else 0.0,
        "cocycle_floor_selected_mean_cycle_lower_bound_normalized_mean": float(np.mean(series_cocycle_cycle_lower_bound_normalized)) if series_cocycle_cycle_lower_bound_normalized else 0.0,
        "frame_stability_vs_negative_mass_correlation": _pearson(
            series_frame_stability,
            series_negative_ratio,
        ),
        "frame_stability_vs_decomposition_correlation": _pearson(
            series_frame_stability,
            series_stratum_decomposition,
        ),
        "frame_stability_vs_cocycle_floor_correlation": _pearson(
            series_frame_stability,
            series_cocycle_floor,
        ),
        "frame_margin_vs_cocycle_floor_correlation": _pearson(
            series_frame_margin,
            series_cocycle_floor,
        ),
        "frame_margin_vs_cocycle_floor_normalized_lower_bound_correlation": _pearson(
            series_frame_margin,
            series_cocycle_cycle_lower_bound_normalized,
        ),
        "backbone_gap_vs_negative_gap_correlation": _pearson(
            series_positive_gap,
            series_negative_gap,
        ),
        "decomposition_vs_negative_mass_correlation": _pearson(
            series_stratum_decomposition,
            series_negative_ratio,
        ),
    }


def main() -> int:
    args = _parse_args()
    warnings: list[str] = []
    cocycle_payload = _load_json(Path(args.cocycle_floor_json))
    if cocycle_payload is None:
        warnings.append(f"missing or invalid cocycle floor json: {args.cocycle_floor_json}")
    try:
        bundle = _load_raw_bundle(Path(args.raw_archive), warnings)
    except Exception as exc:  # noqa: BLE001
        payload = {
            **CONTROL_CARD,
            "control_card": CONTROL_CARD,
            "contract": CONTRACT,
            "route_decision": ROUTE_DECISION,
            "route_mode": "fail-closed",
            "fail_closed": True,
            "schema_version": SCHEMA_VERSION,
            "script": SCRIPT_NAME,
            "authority": AUTHORITY,
            "status": ERROR_STATUS,
            "ok": False,
            "errors": [str(exc)],
            "warnings": warnings,
            "inputs": {
                "raw_archive": str(args.raw_archive),
                "cocycle_floor_json": str(args.cocycle_floor_json),
                "output_json": str(args.output_json),
            },
            "parameters": {
                "frame": args.frame,
                "frame_limit": args.frame_limit,
                "top_k": int(args.top_k),
                "pool_multiplier": int(args.pool_multiplier),
                "zero_eps": float(args.zero_eps),
                "triad_sample_limit": int(args.triad_sample_limit),
            },
            "triad_frame_stability_rows": [],
        }
        args.output_json.parent.mkdir(parents=True, exist_ok=True)
        args.output_json.write_text(_json_text(payload, args.pretty) + "\n", encoding="utf-8")
        print(_json_text(payload, args.pretty))
        return 1

    slots = _frame_indices(bundle.frame_count, args.frame, args.frame_limit)
    if not slots:
        payload = {
            **CONTROL_CARD,
            "control_card": CONTROL_CARD,
            "contract": CONTRACT,
            "route_decision": ROUTE_DECISION,
            "route_mode": "fail-closed",
            "fail_closed": True,
            "schema_version": SCHEMA_VERSION,
            "script": SCRIPT_NAME,
            "authority": AUTHORITY,
            "status": ERROR_STATUS,
            "ok": False,
            "errors": ["no frames selected for triad frame-stability scan"],
            "warnings": warnings,
            "inputs": {
                "raw_archive": str(args.raw_archive),
                "cocycle_floor_json": str(args.cocycle_floor_json),
                "output_json": str(args.output_json),
            },
            "parameters": {
                "frame": args.frame,
                "frame_limit": args.frame_limit,
                "top_k": int(args.top_k),
                "pool_multiplier": int(args.pool_multiplier),
                "zero_eps": float(args.zero_eps),
                "triad_sample_limit": int(args.triad_sample_limit),
            },
            "triad_frame_stability_rows": [],
        }
        args.output_json.parent.mkdir(parents=True, exist_ok=True)
        args.output_json.write_text(_json_text(payload, args.pretty) + "\n", encoding="utf-8")
        print(_json_text(payload, args.pretty))
        return 1

    rows: list[dict[str, Any]] = []
    counts = {OK_STATUS: 0, PARTIAL_STATUS: 0, ERROR_STATUS: 0}
    cocycle_floor_by_frame = _select_cocycle_floor_carrier(cocycle_payload)
    for slot in slots:
        status, row = _evaluate_frame(
            slot=slot,
            snapshot=slot,
            bundle=bundle,
            cocycle_floor_record=cocycle_floor_by_frame.get(int(slot)),
            top_k=int(args.top_k),
            pool_multiplier=int(args.pool_multiplier),
            zero_eps=float(args.zero_eps),
            triad_sample_limit=int(args.triad_sample_limit),
        )
        counts[status] = counts.get(status, 0) + 1
        rows.append(row)

    aggregate = _aggregate_rows(rows)
    status = OK_STATUS if counts.get(ERROR_STATUS, 0) == 0 and counts.get(PARTIAL_STATUS, 0) == 0 else PARTIAL_STATUS
    if counts.get(ERROR_STATUS, 0) == len(rows) and rows:
        status = ERROR_STATUS

    payload = {
        **CONTROL_CARD,
        "control_card": CONTROL_CARD,
        "contract": CONTRACT,
        "route_decision": ROUTE_DECISION,
        "route_mode": "fail-closed",
        "fail_closed": True,
        "schema_version": SCHEMA_VERSION,
        "script": SCRIPT_NAME,
        "authority": AUTHORITY,
        "status": status,
        "ok": status == OK_STATUS,
        "inputs": {
            "raw_archive": str(args.raw_archive),
            "cocycle_floor_json": str(args.cocycle_floor_json),
            "output_json": str(args.output_json),
            "frame": args.frame,
            "frame_limit": args.frame_limit,
        },
        "parameters": {
            "frame": args.frame,
            "frame_limit": args.frame_limit,
            "top_k": int(args.top_k),
            "pool_multiplier": int(args.pool_multiplier),
            "zero_eps": float(args.zero_eps),
            "triad_sample_limit": int(args.triad_sample_limit),
        },
        "triad_frame_stability_rows": rows,
        "aggregate": aggregate,
        "warnings": warnings,
        "errors": [],
    }

    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(_json_text(payload, args.pretty) + "\n", encoding="utf-8")
    print(_json_text(payload, args.pretty))
    return 0 if status != ERROR_STATUS else 1


if __name__ == "__main__":
    raise SystemExit(main())
