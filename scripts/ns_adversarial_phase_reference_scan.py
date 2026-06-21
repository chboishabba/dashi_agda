#!/usr/bin/env python3
"""Scan adversarial phase-reference candidates on the raw N128 archive.

The scan compares a small family of global and simple geometry-aware phase
references against the same selected-mode triads used by the orbit/coherence
tranche.  For each frame it reports the reference that maximizes the
constructive triad score inside that restricted family, along with explicit
zero-phase comparison metrics that make the geometry dependence visible.
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
    ModeRecord,
    _collect_modes,
    _frame_velocity,
    _json_text,
    _load_raw_bundle,
    _scalar_vorticity_spectrum,
    _triad_metrics,
)


SCRIPT_NAME = "scripts/ns_adversarial_phase_reference_scan.py"
CONTRACT = "ns_adversarial_phase_reference_scan"
ROUTE_DECISION = "FAIL_CLOSED_NS_ADVERSARIAL_PHASE_REFERENCE_SCAN"
SCHEMA_VERSION = "1.0.0"

OK_STATUS = "ok"
PARTIAL_STATUS = "partial"
ERROR_STATUS = "error"

DEFAULT_RAW_ARCHIVE = Path(
    "/home/c/Documents/code/dashiCFD/outputs/"
    "sprint65_pressure_reconstruction_N128_seed0_gpu/ns3d_N128_seed0_gpu_pressure.npz"
)
DEFAULT_OUTPUT_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_adversarial_phase_reference_scan_N128_20260621.json"
)
DEFAULT_TOP_K = 48
DEFAULT_POOL_MULTIPLIER = 24
DEFAULT_ZERO_EPS = 1.0e-12
DEFAULT_STRUCTURED_SLOPES = (-1.0, -0.5, 0.5, 1.0)
REFERENCE_FAMILY_LABEL = "global_constant_plus_shell_affine"

CONTROL_CARD = {
    "O": "Scan adversarial phase-reference candidates for the raw N128 triad proxy.",
    "R": (
        "Compare a small family of global and shell-affine phase references against the same selected "
        "modes, then report the reference that maximizes constructive triad score."
    ),
    "C": SCRIPT_NAME,
    "S": "Telemetry only; the winning reference is empirical and not a theorem or route promotion.",
    "L": (
        "Load raw frames, build selected Fourier-vorticity modes, evaluate candidate phase references, "
        "and emit fail-closed per-frame and aggregate telemetry."
    ),
    "P": ROUTE_DECISION,
    "G": "No theorem, Clay, or promotion claim is inferred from the reference winner.",
    "F": "A zero-phase baseline is not privileged; the geometry-dependent candidate family may choose another reference.",
}

AUTHORITY = {
    "candidate_only": True,
    "empirical_non_promoting": True,
    "truth_authority": False,
    "theorem_authority": False,
    "clay_authority": False,
    "runtime_authority": False,
    "promoted": False,
}

NON_PROMOTION_MARKERS = {
    "candidate_only": True,
    "empirical_non_promoting": True,
    "promotion_claim": False,
    "theorem_claim": False,
    "clay_claim": False,
    "route_promoted": False,
    "best_reference_promoted": False,
}


@dataclass(frozen=True)
class ReferenceCandidateSpec:
    reference_id: str
    reference_kind: str
    phase_slope: float
    weight_power: float
    uses_shell_geometry: bool


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--raw-archive", type=Path, default=DEFAULT_RAW_ARCHIVE)
    parser.add_argument("--output-json", type=Path, default=DEFAULT_OUTPUT_JSON)
    parser.add_argument("--frame", type=int, default=None)
    parser.add_argument("--frame-limit", type=int, default=None)
    parser.add_argument("--top-k", type=int, default=DEFAULT_TOP_K)
    parser.add_argument("--pool-multiplier", type=int, default=DEFAULT_POOL_MULTIPLIER)
    parser.add_argument("--zero-eps", type=float, default=DEFAULT_ZERO_EPS)
    parser.add_argument("--pretty", action="store_true")
    return parser.parse_args()


def _json_text(payload: dict[str, Any], pretty: bool) -> str:
    if pretty:
        return json.dumps(payload, sort_keys=True, indent=2, allow_nan=False)
    return json.dumps(payload, sort_keys=True, separators=(",", ":"), allow_nan=False)


def _finite_float(value: Any) -> float | None:
    if value is None or isinstance(value, bool):
        return None
    try:
        parsed = float(value)
    except (TypeError, ValueError):
        return None
    return parsed if math.isfinite(parsed) else None


def _nonnegative_int(value: Any) -> int | None:
    if isinstance(value, bool):
        return None
    if isinstance(value, int):
        return value if value >= 0 else None
    if isinstance(value, float) and math.isfinite(value) and value.is_integer() and value >= 0.0:
        return int(value)
    return None


def _wrap_phase(value: np.ndarray | float) -> np.ndarray | float:
    return np.arctan2(np.sin(value), np.cos(value))


def _mean_or_none(values: list[float]) -> float | None:
    if not values:
        return None
    return float(np.mean(np.asarray(values, dtype=np.float64)))


def _reference_weight(amplitudes: np.ndarray, power: float) -> np.ndarray:
    weights = np.power(np.asarray(amplitudes, dtype=np.float64), float(power))
    if not np.all(np.isfinite(weights)):
        raise ValueError("reference weights must be finite")
    return weights


def _weighted_phase_offset(phases: np.ndarray, weights: np.ndarray) -> float:
    vector = np.sum(weights * np.exp(1.0j * phases))
    magnitude = float(abs(vector))
    if magnitude <= 0.0:
        return 0.0
    return float(math.atan2(vector.imag, vector.real))


def _shift_modes(modes: list[ModeRecord], shift: np.ndarray) -> list[ModeRecord]:
    return [
        ModeRecord(
            key=mode.key,
            amplitude=mode.amplitude,
            phase=float(_wrap_phase(mode.phase - shift[index])),
            shell_radius=mode.shell_radius,
        )
        for index, mode in enumerate(modes)
    ]


def _reference_specs() -> list[ReferenceCandidateSpec]:
    specs = [
        ReferenceCandidateSpec(
            reference_id="zero",
            reference_kind="global",
            phase_slope=0.0,
            weight_power=1.0,
            uses_shell_geometry=False,
        ),
        ReferenceCandidateSpec(
            reference_id="global_resultant",
            reference_kind="global",
            phase_slope=0.0,
            weight_power=1.0,
            uses_shell_geometry=False,
        ),
        ReferenceCandidateSpec(
            reference_id="global_energy_resultant",
            reference_kind="global",
            phase_slope=0.0,
            weight_power=2.0,
            uses_shell_geometry=False,
        ),
        ReferenceCandidateSpec(
            reference_id="dominant_mode_anchor",
            reference_kind="global",
            phase_slope=0.0,
            weight_power=1.0,
            uses_shell_geometry=False,
        ),
    ]
    for slope in DEFAULT_STRUCTURED_SLOPES:
        specs.append(
            ReferenceCandidateSpec(
                reference_id=f"shell_affine_{slope:+.2f}",
                reference_kind="structured",
                phase_slope=float(slope),
                weight_power=1.0,
                uses_shell_geometry=True,
            )
        )
    return specs


def _reference_shift(
    spec: ReferenceCandidateSpec,
    phases: np.ndarray,
    amplitudes: np.ndarray,
    shell_coord: np.ndarray,
) -> tuple[float, np.ndarray]:
    if spec.reference_id == "zero":
        offset = 0.0
        slope = 0.0
    elif spec.reference_id == "dominant_mode_anchor":
        offset = float(phases[int(np.argmax(amplitudes))]) if len(phases) else 0.0
        slope = 0.0
    else:
        slope = float(spec.phase_slope)
        if spec.uses_shell_geometry:
            base_phases = phases - (slope * shell_coord)
        else:
            base_phases = phases
        weights = _reference_weight(amplitudes, spec.weight_power)
        offset = _weighted_phase_offset(np.asarray(base_phases, dtype=np.float64), weights)
    shift = offset + (slope * shell_coord)
    return offset, np.asarray(shift, dtype=np.float64)


def _candidate_metrics(
    modes: list[ModeRecord],
    spec: ReferenceCandidateSpec,
    zero_eps: float,
    phases: np.ndarray,
    amplitudes: np.ndarray,
    shell_coord: np.ndarray,
) -> dict[str, Any]:
    offset, shift = _reference_shift(spec, phases, amplitudes, shell_coord)
    adjusted_modes = _shift_modes(modes, shift)
    metrics = _triad_metrics(adjusted_modes, zero_eps=zero_eps)
    shift_rms = float(math.sqrt(float(np.mean(np.square(_wrap_phase(shift)))))) if len(shift) else 0.0
    return {
        "reference_id": spec.reference_id,
        "reference_kind": spec.reference_kind,
        "phase_slope": float(spec.phase_slope),
        "phase_offset": float(_wrap_phase(offset)),
        "phase_shift_rms": shift_rms,
        "constructive_weight_fraction": float(metrics["constructive_weight_fraction"]),
        "orbit_coherence": float(metrics["orbit_coherence"]),
        "phase_alignment_fraction": float(metrics["phase_alignment_fraction"]),
        "phase_bias": float(metrics["phase_bias"]),
        "orbit_phase_strength": float(metrics["orbit_phase_strength"]),
        "triad_count": int(metrics["triad_count"]),
    }


def _build_candidate_rows(
    modes: list[ModeRecord],
    zero_eps: float,
) -> tuple[list[dict[str, Any]], dict[str, Any], dict[str, Any], dict[str, Any]]:
    if len(modes) < 3:
        empty = {}
        return [], empty, empty, empty

    amplitudes = np.asarray([mode.amplitude for mode in modes], dtype=np.float64)
    phases = np.asarray([mode.phase for mode in modes], dtype=np.float64)
    shell_radii = np.asarray([mode.shell_radius for mode in modes], dtype=np.float64)
    shell_center = float(np.mean(shell_radii))
    shell_span = float(np.max(shell_radii) - np.min(shell_radii))
    shell_scale = shell_span if shell_span > float(zero_eps) else 1.0
    shell_coord = (shell_radii - shell_center) / shell_scale

    specs = _reference_specs()
    candidates = [
        _candidate_metrics(
            modes=modes,
            spec=spec,
            zero_eps=zero_eps,
            phases=phases,
            amplitudes=amplitudes,
            shell_coord=shell_coord,
        )
        for spec in specs
    ]
    candidates.sort(
        key=lambda row: (
            float(row["constructive_weight_fraction"]),
            float(row["orbit_coherence"]),
            float(row["phase_alignment_fraction"]),
            float(row["orbit_phase_strength"]),
            -abs(float(row["phase_slope"])),
        ),
        reverse=True,
    )
    for rank, row in enumerate(candidates, start=1):
        row["reference_rank"] = int(rank)

    by_id = {row["reference_id"]: row for row in candidates}
    zero_row = by_id["zero"]
    global_rows = [row for row in candidates if row["reference_kind"] == "global"]
    structured_rows = [row for row in candidates if row["reference_kind"] == "structured"]
    best_global = global_rows[0] if global_rows else {}
    best_structured = structured_rows[0] if structured_rows else {}

    return candidates, zero_row, best_global, best_structured


def _evaluate_frame(
    slot: int,
    snapshot: int,
    bundle: Any,
    top_k: int,
    pool_multiplier: int,
    zero_eps: float,
) -> tuple[str, dict[str, Any]]:
    row: dict[str, Any] = {
        "frame": int(slot),
        "snapshot_index": int(snapshot),
        "orbit_phase": float(snapshot),
        "source": str(bundle.path),
        "top_k": int(top_k),
        "pool_multiplier": int(pool_multiplier),
        "reference_family": REFERENCE_FAMILY_LABEL,
        "non_promoting": True,
        "promotion_claim": False,
        "theorem_claim": False,
        "clay_claim": False,
    }
    try:
        u, v, w = _frame_velocity(bundle, snapshot)
        spectrum = _scalar_vorticity_spectrum(u, v, w, bundle.domain_length)
        modes = _collect_modes(
            spectrum,
            top_k=top_k,
            zero_eps=zero_eps,
            pool_multiplier=pool_multiplier,
        )
        base_metrics = _triad_metrics(modes, zero_eps=zero_eps)
        if int(base_metrics["triad_count"]) <= 0:
            row.update(
                {
                    "status": PARTIAL_STATUS,
                    "warnings": ["no selected resonant triads found for phase-reference comparison"],
                    "selected_mode_count": int(base_metrics["selected_mode_count"]),
                    "triad_count": 0,
                    "mode_concentration_fraction": float(base_metrics["mode_concentration_fraction"]),
                    "shell_radius_mean": float(base_metrics["shell_radius_mean"]),
                    "triad_shell_spread_mean": float(base_metrics["triad_shell_spread_mean"]),
                    "reference_candidate_count": 0,
                    "reference_candidates": [],
                    "best_reference_id": None,
                    "best_reference_kind": None,
                    "best_reference_rank": None,
                    "best_reference_phase_slope": None,
                    "best_reference_phase_offset": None,
                    "best_reference_phase_shift_rms": None,
                    "best_constructive_weight_fraction": None,
                    "best_orbit_coherence": None,
                    "best_phase_alignment_fraction": None,
                    "best_phase_bias": None,
                    "best_orbit_phase_strength": None,
                    "zero_reference_rank": None,
                    "zero_reference_constructive_weight_fraction": None,
                    "best_global_reference_id": None,
                    "best_global_reference_rank": None,
                    "best_global_constructive_weight_fraction": None,
                    "best_structured_reference_id": None,
                    "best_structured_reference_rank": None,
                    "best_structured_constructive_weight_fraction": None,
                    "best_minus_zero_constructive_gap": None,
                    "best_minus_best_global_gap": None,
                    "best_structured_minus_best_global_gap": None,
                    "winner_is_zero_reference": False,
                    "winner_is_structured_reference": False,
                    "reference_geometry_gap_visible": False,
                }
            )
            return PARTIAL_STATUS, row

        candidates, zero_row, best_global, best_structured = _build_candidate_rows(
            modes,
            zero_eps=zero_eps,
        )
        if not candidates:
            row["status"] = PARTIAL_STATUS
            row["warnings"] = ["phase-reference family unavailable after triad selection"]
            return PARTIAL_STATUS, row

        winner = candidates[0]
        row.update(
            {
                "status": OK_STATUS,
                "selected_mode_count": int(base_metrics["selected_mode_count"]),
                "triad_count": int(base_metrics["triad_count"]),
                "mode_concentration_fraction": float(base_metrics["mode_concentration_fraction"]),
                "shell_radius_mean": float(base_metrics["shell_radius_mean"]),
                "triad_shell_spread_mean": float(base_metrics["triad_shell_spread_mean"]),
                "reference_candidate_count": int(len(candidates)),
                "reference_candidates": candidates,
                "best_reference_id": winner["reference_id"],
                "best_reference_kind": winner["reference_kind"],
                "best_reference_rank": int(winner["reference_rank"]),
                "best_reference_phase_slope": float(winner["phase_slope"]),
                "best_reference_phase_offset": float(winner["phase_offset"]),
                "best_reference_phase_shift_rms": float(winner["phase_shift_rms"]),
                "best_constructive_weight_fraction": float(winner["constructive_weight_fraction"]),
                "best_orbit_coherence": float(winner["orbit_coherence"]),
                "best_phase_alignment_fraction": float(winner["phase_alignment_fraction"]),
                "best_phase_bias": float(winner["phase_bias"]),
                "best_orbit_phase_strength": float(winner["orbit_phase_strength"]),
                "zero_reference_rank": int(zero_row["reference_rank"]),
                "zero_reference_constructive_weight_fraction": float(zero_row["constructive_weight_fraction"]),
                "best_global_reference_id": best_global.get("reference_id"),
                "best_global_reference_rank": int(best_global["reference_rank"]) if best_global else None,
                "best_global_constructive_weight_fraction": float(best_global["constructive_weight_fraction"]) if best_global else None,
                "best_structured_reference_id": best_structured.get("reference_id"),
                "best_structured_reference_rank": int(best_structured["reference_rank"]) if best_structured else None,
                "best_structured_constructive_weight_fraction": float(best_structured["constructive_weight_fraction"]) if best_structured else None,
                "best_minus_zero_constructive_gap": float(
                    winner["constructive_weight_fraction"] - zero_row["constructive_weight_fraction"]
                ),
                "best_minus_best_global_gap": float(
                    winner["constructive_weight_fraction"] - best_global["constructive_weight_fraction"]
                )
                if best_global
                else None,
                "best_structured_minus_best_global_gap": float(
                    best_structured["constructive_weight_fraction"] - best_global["constructive_weight_fraction"]
                )
                if best_structured and best_global
                else None,
                "winner_is_zero_reference": bool(winner["reference_id"] == "zero"),
                "winner_is_structured_reference": bool(winner["reference_kind"] == "structured"),
                "reference_geometry_gap_visible": bool(
                    winner["reference_id"] != "zero"
                    and (
                        winner["reference_kind"] == "structured"
                        or winner["constructive_weight_fraction"] > zero_row["constructive_weight_fraction"]
                    )
                ),
            }
        )
    except Exception as exc:  # noqa: BLE001
        row["status"] = ERROR_STATUS
        row["errors"] = [f"frame_phase_reference_scan_error: {exc}"]
        return ERROR_STATUS, row

    return OK_STATUS, row


def _aggregate_rows(rows: list[dict[str, Any]], zero_eps: float) -> dict[str, Any]:
    ok_rows = [row for row in rows if row.get("status") == OK_STATUS]
    if not ok_rows:
        return {
            "processed_frames": len(rows),
            "ok_frames": 0,
            "partial_frames": sum(1 for row in rows if row.get("status") == PARTIAL_STATUS),
            "error_frames": sum(1 for row in rows if row.get("status") == ERROR_STATUS),
            "reference_family": REFERENCE_FAMILY_LABEL,
            "top_k": None,
            "pool_multiplier": None,
            "zero_eps": None,
            "reference_candidate_count": None,
            "best_reference_is_zero_fraction": None,
            "best_reference_is_structured_fraction": None,
            "zero_reference_rank_mean": None,
            "zero_reference_constructive_weight_fraction_mean": None,
            "best_constructive_weight_fraction_mean": None,
            "best_global_constructive_weight_fraction_mean": None,
            "best_structured_constructive_weight_fraction_mean": None,
            "best_minus_zero_constructive_gap_mean": None,
            "best_minus_best_global_gap_mean": None,
            "best_structured_minus_best_global_gap_mean": None,
            "mode_concentration_fraction_mean": None,
            "triad_shell_spread_mean": None,
            "gap_vs_shell_spread_correlation": None,
            "winner_zero_rank_fraction": None,
        }

    def _series(key: str) -> list[float]:
        values: list[float] = []
        for row in ok_rows:
            parsed = _finite_float(row.get(key))
            if parsed is not None:
                values.append(parsed)
        return values

    zero_ranks = [float(row["zero_reference_rank"]) for row in ok_rows if _nonnegative_int(row.get("zero_reference_rank")) is not None]
    constructive = _series("best_constructive_weight_fraction")
    global_constructive = _series("best_global_constructive_weight_fraction")
    structured_constructive = _series("best_structured_constructive_weight_fraction")
    best_minus_zero = _series("best_minus_zero_constructive_gap")
    best_minus_global = _series("best_minus_best_global_gap")
    structured_minus_global = _series("best_structured_minus_best_global_gap")
    shell_spread = _series("triad_shell_spread_mean")

    return {
        "processed_frames": len(rows),
        "ok_frames": len(ok_rows),
        "partial_frames": sum(1 for row in rows if row.get("status") == PARTIAL_STATUS),
        "error_frames": sum(1 for row in rows if row.get("status") == ERROR_STATUS),
        "reference_family": REFERENCE_FAMILY_LABEL,
        "top_k": int(ok_rows[0].get("top_k", DEFAULT_TOP_K)),
        "pool_multiplier": int(ok_rows[0].get("pool_multiplier", DEFAULT_POOL_MULTIPLIER)),
        "zero_eps": float(zero_eps),
        "reference_candidate_count": int(ok_rows[0].get("reference_candidate_count", 0)),
        "best_reference_is_zero_fraction": float(
            np.mean([1.0 if row.get("winner_is_zero_reference") else 0.0 for row in ok_rows])
        ),
        "best_reference_is_structured_fraction": float(
            np.mean([1.0 if row.get("winner_is_structured_reference") else 0.0 for row in ok_rows])
        ),
        "zero_reference_rank_mean": _mean_or_none(zero_ranks),
        "zero_reference_constructive_weight_fraction_mean": _mean_or_none(
            [float(row["zero_reference_constructive_weight_fraction"]) for row in ok_rows]
        ),
        "best_constructive_weight_fraction_mean": _mean_or_none(constructive),
        "best_global_constructive_weight_fraction_mean": _mean_or_none(global_constructive),
        "best_structured_constructive_weight_fraction_mean": _mean_or_none(structured_constructive),
        "best_minus_zero_constructive_gap_mean": _mean_or_none(best_minus_zero),
        "best_minus_best_global_gap_mean": _mean_or_none(best_minus_global),
        "best_structured_minus_best_global_gap_mean": _mean_or_none(structured_minus_global),
        "mode_concentration_fraction_mean": _mean_or_none(
            [float(row["mode_concentration_fraction"]) for row in ok_rows]
        ),
        "triad_shell_spread_mean": _mean_or_none(shell_spread),
        "gap_vs_shell_spread_correlation": _pearson(
            [float(row["best_minus_zero_constructive_gap"]) for row in ok_rows],
            shell_spread,
        )
        if len(shell_spread) >= 2
        else None,
        "winner_zero_rank_fraction": float(
            np.mean([1.0 if row.get("winner_is_zero_reference") else 0.0 for row in ok_rows])
        ),
    }


def main() -> int:
    args = _parse_args()
    warnings: list[str] = []
    try:
        bundle = _load_raw_bundle(Path(args.raw_archive), warnings)
    except Exception as exc:  # noqa: BLE001
        payload = {
            **CONTROL_CARD,
            "control_card": CONTROL_CARD,
            "contract": CONTRACT,
            "route_decision": ROUTE_DECISION,
            "schema_version": SCHEMA_VERSION,
            "script": SCRIPT_NAME,
            "authority": AUTHORITY,
            "non_promotion_markers": NON_PROMOTION_MARKERS,
            "status": ERROR_STATUS,
            "warnings": warnings,
            "errors": [str(exc)],
        }
        args.output_json.parent.mkdir(parents=True, exist_ok=True)
        args.output_json.write_text(_json_text(payload, args.pretty) + "\n", encoding="utf-8")
        print(_json_text(payload, args.pretty))
        return 1

    slots = _frame_indices(bundle.frame_count, args.frame, args.frame_limit)
    rows: list[dict[str, Any]] = []
    counts = {OK_STATUS: 0, PARTIAL_STATUS: 0, ERROR_STATUS: 0}
    for slot in slots:
        status, row = _evaluate_frame(
            slot=slot,
            snapshot=slot,
            bundle=bundle,
            top_k=int(args.top_k),
            pool_multiplier=int(args.pool_multiplier),
            zero_eps=float(args.zero_eps),
        )
        counts[status] = counts.get(status, 0) + 1
        rows.append(row)

    aggregate = _aggregate_rows(rows, zero_eps=float(args.zero_eps))
    status = OK_STATUS
    errors_out: list[str] = []
    if not rows:
        status = ERROR_STATUS
        errors_out.append("no frames selected")
    elif counts.get(ERROR_STATUS, 0) > 0 or counts.get(PARTIAL_STATUS, 0) > 0:
        status = PARTIAL_STATUS

    payload = {
        **CONTROL_CARD,
        "control_card": CONTROL_CARD,
        "contract": CONTRACT,
        "route_decision": ROUTE_DECISION,
        "schema_version": SCHEMA_VERSION,
        "script": SCRIPT_NAME,
        "authority": AUTHORITY,
        "non_promotion_markers": NON_PROMOTION_MARKERS,
        "inputs": {
            "raw_archive": str(args.raw_archive),
            "output_json": str(args.output_json),
        },
        "parameters": {
            "top_k": int(args.top_k),
            "pool_multiplier": int(args.pool_multiplier),
            "zero_eps": float(args.zero_eps),
            "frame": args.frame,
            "frame_limit": args.frame_limit,
            "structured_slopes": list(DEFAULT_STRUCTURED_SLOPES),
        },
        "status": status,
        "warnings": warnings,
        "errors": errors_out,
        "aggregate": aggregate,
        "phase_reference_rows": rows,
    }

    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(_json_text(payload, args.pretty) + "\n", encoding="utf-8")
    print(_json_text(payload, args.pretty))
    return 0 if status == OK_STATUS else 1


if __name__ == "__main__":
    raise SystemExit(main())
