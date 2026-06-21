#!/usr/bin/env python3
"""Compare orbit-coherence telemetry to same-amplitude phase-shuffled controls."""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any

import numpy as np

from ns_boundary_pressure_gate_scan import _frame_indices, _pearson  # type: ignore
from ns_orbit_phase_coherence_scan import (  # type: ignore
    AUTHORITY,
    CONTROL_CARD as ORBIT_CARD,
    ModeRecord,
    _collect_modes,
    _frame_velocity,
    _json_text,
    _load_raw_bundle,
    _scalar_vorticity_spectrum,
    _triad_metrics,
)


SCRIPT_NAME = "scripts/ns_non_sobolev_coherence_gate_scan.py"
CONTRACT = "ns_non_sobolev_coherence_gate_scan"
ROUTE_DECISION = "FAIL_CLOSED_NS_NON_SOBOLEV_COHERENCE_GATE_SCAN"
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
    "ns_non_sobolev_telemetry_scan_N128_20260621.json"
)
DEFAULT_TOP_K = 48
DEFAULT_POOL_MULTIPLIER = 24
DEFAULT_SURROGATE_COUNT = 6
DEFAULT_ZERO_EPS = 1.0e-12
DEFAULT_HS_EXPONENT = 2.5

CONTROL_CARD = {
    "O": "Measure a candidate non-Sobolev coherence gate using same-amplitude phase-shuffled controls.",
    "R": (
        "Compare the observed orbit-phase coherence proxy to surrogate phase-shuffled controls with "
        "the same amplitude data, so the global H^s-size proxy is held fixed while phase structure changes."
    ),
    "C": SCRIPT_NAME,
    "S": "Telemetry only; numerical non-equivalence is evidence of distinctness, not a bridge theorem.",
    "L": (
        "Load raw frames, compute observed coherence, generate same-amplitude phase surrogates, "
        "compare coherence margins, and emit fail-closed telemetry."
    ),
    "P": ROUTE_DECISION,
    "G": "No theorem, Clay, or proof claim is inferred from this scan.",
    "F": "Distinctness from a Sobolev-size proxy remains numerical telemetry rather than a proof of a non-circular bridge.",
}


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--raw-archive", type=Path, default=DEFAULT_RAW_ARCHIVE)
    parser.add_argument("--output-json", type=Path, default=DEFAULT_OUTPUT_JSON)
    parser.add_argument("--frame", type=int, default=None)
    parser.add_argument("--frame-limit", type=int, default=None)
    parser.add_argument("--top-k", type=int, default=DEFAULT_TOP_K)
    parser.add_argument("--pool-multiplier", type=int, default=DEFAULT_POOL_MULTIPLIER)
    parser.add_argument("--surrogate-count", type=int, default=DEFAULT_SURROGATE_COUNT)
    parser.add_argument("--hs-exponent", type=float, default=DEFAULT_HS_EXPONENT)
    parser.add_argument("--zero-eps", type=float, default=DEFAULT_ZERO_EPS)
    parser.add_argument("--seed", type=int, default=20260621)
    parser.add_argument("--pretty", action="store_true")
    return parser.parse_args()


def _velocity_hs_norm(
    u: np.ndarray,
    v: np.ndarray,
    w: np.ndarray,
    domain_length: float,
    exponent: float,
) -> float:
    n = int(u.shape[0])
    spacing = float(domain_length) / float(n)
    base = 2.0 * math.pi * np.fft.fftfreq(n, d=spacing)
    kx = base.reshape(n, 1, 1)
    ky = base.reshape(1, n, 1)
    kz = base.reshape(1, 1, n)
    k2 = (kx * kx) + (ky * ky) + (kz * kz)
    weight = np.power(1.0 + k2, float(exponent))
    u_hat = np.fft.fftn(u, axes=(0, 1, 2))
    v_hat = np.fft.fftn(v, axes=(0, 1, 2))
    w_hat = np.fft.fftn(w, axes=(0, 1, 2))
    total = np.sum(weight * (np.abs(u_hat) ** 2 + np.abs(v_hat) ** 2 + np.abs(w_hat) ** 2))
    return float(math.sqrt(max(float(total), 0.0)))


def _modes_with_replaced_phases(modes: list[ModeRecord], phases: np.ndarray) -> list[ModeRecord]:
    return [
        ModeRecord(
            key=mode.key,
            amplitude=mode.amplitude,
            phase=float(phases[index]),
            shell_radius=mode.shell_radius,
        )
        for index, mode in enumerate(modes)
    ]


def _surrogate_metrics(
    modes: list[ModeRecord],
    surrogate_count: int,
    zero_eps: float,
    seed: int,
) -> tuple[float, float, float]:
    if len(modes) < 3 or surrogate_count <= 0:
        return 0.0, 0.0, 0.0

    rng = np.random.default_rng(seed)
    phases = np.asarray([mode.phase for mode in modes], dtype=np.float64)
    coherence_values: list[float] = []
    bias_values: list[float] = []
    strength_values: list[float] = []
    for _ in range(int(surrogate_count)):
        shuffled = np.asarray(phases[rng.permutation(len(phases))], dtype=np.float64)
        metrics = _triad_metrics(_modes_with_replaced_phases(modes, shuffled), zero_eps=zero_eps)
        coherence_values.append(float(metrics["orbit_coherence"]))
        bias_values.append(float(metrics["phase_bias"]))
        strength_values.append(float(metrics["orbit_phase_strength"]))
    return (
        float(np.mean(coherence_values)) if coherence_values else 0.0,
        float(np.mean(bias_values)) if bias_values else 0.0,
        float(np.mean(strength_values)) if strength_values else 0.0,
    )


def _evaluate_frame(
    slot: int,
    snapshot: int,
    bundle: Any,
    top_k: int,
    pool_multiplier: int,
    surrogate_count: int,
    hs_exponent: float,
    zero_eps: float,
    seed: int,
) -> tuple[str, dict[str, Any]]:
    row: dict[str, Any] = {
        "frame": int(slot),
        "snapshot_index": int(snapshot),
        "orbit_phase": float(snapshot),
        "source": str(bundle.path),
    }
    try:
        u, v, w = _frame_velocity(bundle, snapshot)
        hs_norm = _velocity_hs_norm(u, v, w, bundle.domain_length, hs_exponent)
        spectrum = _scalar_vorticity_spectrum(u, v, w, bundle.domain_length)
        modes = _collect_modes(
            spectrum,
            top_k=top_k,
            zero_eps=zero_eps,
            pool_multiplier=pool_multiplier,
        )
        observed = _triad_metrics(modes, zero_eps=zero_eps)
        surrogate_coherence, surrogate_bias, surrogate_strength = _surrogate_metrics(
            modes=modes,
            surrogate_count=surrogate_count,
            zero_eps=zero_eps,
            seed=seed + int(snapshot),
        )
    except Exception as exc:  # noqa: BLE001
        row["status"] = ERROR_STATUS
        row["errors"] = [f"frame_non_sobolev_scan_error: {exc}"]
        return ERROR_STATUS, row

    row.update(
        {
            "same_hs_norm_control": True,
            "hs_exponent": float(hs_exponent),
            "hs_norm": hs_norm,
            "observed_orbit_coherence": float(observed["orbit_coherence"]),
            "observed_phase_bias": float(observed["phase_bias"]),
            "observed_phase_strength": float(observed["orbit_phase_strength"]),
            "surrogate_coherence_mean": surrogate_coherence,
            "surrogate_phase_bias_mean": surrogate_bias,
            "surrogate_phase_strength_mean": surrogate_strength,
            "non_sobolev_margin": float(observed["orbit_coherence"] - surrogate_coherence),
            "non_sobolev_score": float(observed["phase_bias"] - surrogate_bias),
            "non_sobolev_strength_gap": float(observed["orbit_phase_strength"] - surrogate_strength),
            "triad_count": int(observed["triad_count"]),
            "selected_mode_count": int(observed["selected_mode_count"]),
        }
    )

    if int(observed["triad_count"]) <= 0:
        row["status"] = PARTIAL_STATUS
        row["warnings"] = ["no selected resonant triads for observed scan"]
        return PARTIAL_STATUS, row

    row["status"] = OK_STATUS
    return OK_STATUS, row


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
            "status": ERROR_STATUS,
            "errors": [str(exc)],
            "warnings": warnings,
        }
        args.output_json.parent.mkdir(parents=True, exist_ok=True)
        args.output_json.write_text(_json_text(payload, args.pretty) + "\n", encoding="utf-8")
        print(_json_text(payload, args.pretty))
        return 1

    rows: list[dict[str, Any]] = []
    counts = {OK_STATUS: 0, PARTIAL_STATUS: 0, ERROR_STATUS: 0}
    slots = _frame_indices(bundle.frame_count, args.frame, args.frame_limit)
    for slot in slots:
        status, row = _evaluate_frame(
            slot=slot,
            snapshot=slot,
            bundle=bundle,
            top_k=int(args.top_k),
            pool_multiplier=int(args.pool_multiplier),
            surrogate_count=int(args.surrogate_count),
            hs_exponent=float(args.hs_exponent),
            zero_eps=float(args.zero_eps),
            seed=int(args.seed),
        )
        counts[status] = counts.get(status, 0) + 1
        rows.append(row)

    ok_rows = [row for row in rows if row.get("status") == OK_STATUS]
    aggregate = {
        "processed_frames": len(rows),
        "ok_frames": counts.get(OK_STATUS, 0),
        "partial_frames": counts.get(PARTIAL_STATUS, 0),
        "error_frames": counts.get(ERROR_STATUS, 0),
        "hs_exponent": float(args.hs_exponent),
        "same_hs_norm_control_fraction": float(np.mean([1.0 if row.get("same_hs_norm_control") else 0.0 for row in rows])) if rows else 0.0,
        "non_sobolev_margin_mean": float(np.mean([row.get("non_sobolev_margin", 0.0) for row in ok_rows])) if ok_rows else 0.0,
        "non_sobolev_score_mean": float(np.mean([row.get("non_sobolev_score", 0.0) for row in ok_rows])) if ok_rows else 0.0,
        "non_sobolev_strength_gap_mean": float(np.mean([row.get("non_sobolev_strength_gap", 0.0) for row in ok_rows])) if ok_rows else 0.0,
        "hs_norm_mean": float(np.mean([row.get("hs_norm", 0.0) for row in ok_rows])) if ok_rows else 0.0,
        "margin_vs_hs_norm_correlation": _pearson(
            [float(row.get("non_sobolev_margin", 0.0)) for row in ok_rows],
            [float(row.get("hs_norm", 0.0)) for row in ok_rows],
        ),
        "observed_vs_surrogate_coherence_correlation": _pearson(
            [float(row.get("observed_orbit_coherence", 0.0)) for row in ok_rows],
            [float(row.get("surrogate_coherence_mean", 0.0)) for row in ok_rows],
        ),
    }

    payload = {
        **CONTROL_CARD,
        "control_card": CONTROL_CARD,
        "contract": CONTRACT,
        "route_decision": ROUTE_DECISION,
        "schema_version": SCHEMA_VERSION,
        "script": SCRIPT_NAME,
        "authority": AUTHORITY,
        "inputs": {
            "raw_archive": str(args.raw_archive),
            "output_json": str(args.output_json),
        },
        "parameters": {
            "top_k": int(args.top_k),
            "pool_multiplier": int(args.pool_multiplier),
            "surrogate_count": int(args.surrogate_count),
            "hs_exponent": float(args.hs_exponent),
            "seed": int(args.seed),
        },
        "status": OK_STATUS if counts.get(ERROR_STATUS, 0) == 0 else PARTIAL_STATUS,
        "warnings": warnings,
        "errors": [],
        "aggregate": aggregate,
        "non_sobolev_rows": rows,
    }
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(_json_text(payload, args.pretty) + "\n", encoding="utf-8")
    print(_json_text(payload, args.pretty))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
