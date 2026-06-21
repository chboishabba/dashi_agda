#!/usr/bin/env python3
"""Scan orbit-level triadic phase coherence proxies on the raw N128 archive."""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Any

import numpy as np

from ns_boundary_pressure_gate_scan import _frame_indices, _pearson  # type: ignore
from ns_pressure_eigenframe_gap_scan import RawBundle, _frame_velocity, _load_raw_bundle  # type: ignore


SCRIPT_NAME = "scripts/ns_orbit_phase_coherence_scan.py"
CONTRACT = "ns_orbit_phase_coherence_scan"
ROUTE_DECISION = "FAIL_CLOSED_NS_ORBIT_PHASE_COHERENCE_SCAN"
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
    "ns_orbit_phase_coherence_scan_N128_20260621.json"
)
DEFAULT_TOP_K = 48
DEFAULT_POOL_MULTIPLIER = 24
DEFAULT_ZERO_EPS = 1.0e-12

CONTROL_CARD = {
    "O": "Measure candidate orbit-level triadic phase-coherence telemetry on the raw N128 archive.",
    "R": (
        "Build a fail-closed triadic coherence proxy from the dominant Fourier-vorticity modes, "
        "using resonant mode triples and weighted phase mismatch statistics."
    ),
    "C": SCRIPT_NAME,
    "S": "Telemetry only; any phase carrier or triad proxy is empirical and non-promoting.",
    "L": (
        "Load raw frames, construct a scalar vorticity spectrum, select dominant modes, "
        "form resonant selected-mode triads, and emit framewise coherence metrics."
    ),
    "P": ROUTE_DECISION,
    "G": "No theorem, Clay, or route promotion is inferred from this scan.",
    "F": "The realized proxy may diagnose phase organization, but it is not a proof of orbit-level phase-locking exclusion.",
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


@dataclass(frozen=True)
class ModeRecord:
    key: tuple[int, int, int]
    amplitude: float
    phase: float
    shell_radius: float


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


def _integer_modes(n: int) -> np.ndarray:
    raw = np.fft.fftfreq(n) * float(n)
    return np.asarray(np.rint(raw), dtype=np.int64)


def _wave_numbers(n: int, domain_length: float) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    spacing = float(domain_length) / float(n)
    base = 2.0 * math.pi * np.fft.fftfreq(n, d=spacing)
    return (
        base.reshape(n, 1, 1),
        base.reshape(1, n, 1),
        base.reshape(1, 1, n),
    )


def _scalar_vorticity_spectrum(
    u: np.ndarray,
    v: np.ndarray,
    w: np.ndarray,
    domain_length: float,
) -> np.ndarray:
    n = int(u.shape[0])
    kx, ky, kz = _wave_numbers(n, domain_length)
    u_hat = np.fft.fftn(u, axes=(0, 1, 2))
    v_hat = np.fft.fftn(v, axes=(0, 1, 2))
    w_hat = np.fft.fftn(w, axes=(0, 1, 2))

    omega_x = 1j * (ky * w_hat - kz * v_hat)
    omega_y = 1j * (kz * u_hat - kx * w_hat)
    omega_z = 1j * (kx * v_hat - ky * u_hat)
    return np.asarray(omega_x + omega_y + omega_z, dtype=np.complex128)


def _top_modes(spectrum: np.ndarray, limit: int, zero_eps: float) -> list[ModeRecord]:
    n = int(spectrum.shape[0])
    integer = _integer_modes(n)
    amplitude = np.abs(spectrum)
    flat = np.argwhere(amplitude > float(zero_eps))
    if flat.size == 0:
        return []

    weights = amplitude[tuple(flat.T)]
    order = np.argsort(weights)[::-1]
    kept = flat[order[: max(0, int(limit))]]

    modes: list[ModeRecord] = []
    for idx in kept:
        i, j, k = (int(x) for x in idx)
        key = (int(integer[i]), int(integer[j]), int(integer[k]))
        if key == (0, 0, 0):
            continue
        value = complex(spectrum[i, j, k])
        amp = float(abs(value))
        if not math.isfinite(amp) or amp <= float(zero_eps):
            continue
        phase = float(math.atan2(value.imag, value.real))
        shell_radius = float(math.sqrt(key[0] ** 2 + key[1] ** 2 + key[2] ** 2))
        modes.append(
            ModeRecord(
                key=key,
                amplitude=amp,
                phase=phase,
                shell_radius=shell_radius,
            )
        )
    return modes


def _triad_supported_modes(modes: list[ModeRecord], top_k: int, zero_eps: float) -> list[ModeRecord]:
    if len(modes) <= max(3, int(top_k)):
        return modes[: max(0, int(top_k))]

    key_to_index = {mode.key: idx for idx, mode in enumerate(modes)}
    participation = np.zeros(len(modes), dtype=np.float64)
    partner_count = np.zeros(len(modes), dtype=np.float64)

    for i, mode_i in enumerate(modes):
        for j in range(i + 1, len(modes)):
            mode_j = modes[j]
            key_k = (
                mode_i.key[0] + mode_j.key[0],
                mode_i.key[1] + mode_j.key[1],
                mode_i.key[2] + mode_j.key[2],
            )
            k_index = key_to_index.get(key_k)
            if k_index is None or k_index == i or k_index == j:
                continue
            mode_k = modes[k_index]
            weight = mode_i.amplitude * mode_j.amplitude * mode_k.amplitude
            if not math.isfinite(weight) or weight <= float(zero_eps):
                continue
            participation[i] += weight
            participation[j] += weight
            participation[k_index] += weight
            partner_count[i] += 1.0
            partner_count[j] += 1.0
            partner_count[k_index] += 1.0

    supported = [idx for idx, score in enumerate(participation) if score > float(zero_eps)]
    if not supported:
        return modes[: max(0, int(top_k))]

    supported.sort(
        key=lambda idx: (
            participation[idx],
            partner_count[idx],
            modes[idx].amplitude,
        ),
        reverse=True,
    )
    selected = sorted(supported[: max(0, int(top_k))])
    return [modes[idx] for idx in selected]


def _collect_modes(
    spectrum: np.ndarray,
    top_k: int,
    zero_eps: float,
    pool_multiplier: int,
) -> list[ModeRecord]:
    candidate_limit = max(int(top_k), int(top_k) * max(1, int(pool_multiplier)))
    candidates = _top_modes(spectrum, limit=candidate_limit, zero_eps=zero_eps)
    return _triad_supported_modes(candidates, top_k=top_k, zero_eps=zero_eps)


def _phase_vector(modes: list[ModeRecord]) -> tuple[np.ndarray, np.ndarray]:
    amplitudes = np.asarray([mode.amplitude for mode in modes], dtype=np.float64)
    phases = np.asarray([mode.phase for mode in modes], dtype=np.float64)
    return amplitudes, phases


def _triad_metrics(modes: list[ModeRecord], zero_eps: float) -> dict[str, Any]:
    if len(modes) < 3:
        return {
            "selected_mode_count": len(modes),
            "triad_count": 0,
            "orbit_coherence": 0.0,
            "phase_alignment_fraction": 0.0,
            "constructive_weight_fraction": 0.0,
            "phase_bias": 0.0,
            "orbit_phase_strength": 0.0,
            "mode_concentration_fraction": 0.0,
            "shell_radius_mean": 0.0,
            "triad_shell_spread_mean": 0.0,
        }

    amplitudes, phases = _phase_vector(modes)
    amp_sum = float(np.sum(amplitudes))
    mode_concentration_fraction = (
        float(np.max(amplitudes)) / amp_sum if amp_sum > float(zero_eps) else 0.0
    )
    shell_radius_mean = float(np.mean([mode.shell_radius for mode in modes]))

    key_to_index = {mode.key: idx for idx, mode in enumerate(modes)}
    total_weight = 0.0
    constructive_weight = 0.0
    weighted_cos = 0.0
    weighted_complex = 0.0 + 0.0j
    spread_accum = 0.0
    triad_count = 0

    for i, mode_i in enumerate(modes):
        for j, mode_j in enumerate(modes):
            if i == j:
                continue
            key_k = (
                mode_i.key[0] + mode_j.key[0],
                mode_i.key[1] + mode_j.key[1],
                mode_i.key[2] + mode_j.key[2],
            )
            k_index = key_to_index.get(key_k)
            if k_index is None or k_index == i or k_index == j:
                continue
            mode_k = modes[k_index]
            weight = mode_i.amplitude * mode_j.amplitude * mode_k.amplitude
            if not math.isfinite(weight) or weight <= float(zero_eps):
                continue
            mismatch = phases[i] + phases[j] - phases[k_index]
            phase_factor = complex(math.cos(mismatch), math.sin(mismatch))
            cos_value = float(phase_factor.real)
            total_weight += weight
            weighted_cos += weight * cos_value
            weighted_complex += weight * phase_factor
            if cos_value > 0.0:
                constructive_weight += weight
            spread_accum += max(mode_i.shell_radius, mode_j.shell_radius, mode_k.shell_radius) - min(
                mode_i.shell_radius, mode_j.shell_radius, mode_k.shell_radius
            )
            triad_count += 1

    if total_weight <= float(zero_eps) or triad_count == 0:
        return {
            "selected_mode_count": len(modes),
            "triad_count": 0,
            "orbit_coherence": 0.0,
            "phase_alignment_fraction": 0.0,
            "constructive_weight_fraction": 0.0,
            "phase_bias": 0.0,
            "orbit_phase_strength": 0.0,
            "mode_concentration_fraction": mode_concentration_fraction,
            "shell_radius_mean": shell_radius_mean,
            "triad_shell_spread_mean": 0.0,
        }

    phase_bias = float(weighted_cos / total_weight)
    orbit_coherence = float(abs(weighted_complex) / total_weight)
    orbit_phase_strength = float(total_weight / max(amp_sum**3, float(zero_eps)))
    return {
        "selected_mode_count": len(modes),
        "triad_count": int(triad_count),
        "orbit_coherence": orbit_coherence,
        "phase_alignment_fraction": 0.5 * (1.0 + phase_bias),
        "constructive_weight_fraction": float(constructive_weight / total_weight),
        "phase_bias": phase_bias,
        "orbit_phase_strength": orbit_phase_strength,
        "mode_concentration_fraction": mode_concentration_fraction,
        "shell_radius_mean": shell_radius_mean,
        "triad_shell_spread_mean": float(spread_accum / float(triad_count)),
    }


def evaluate_frame_orbit_phase(
    bundle: RawBundle,
    slot: int,
    snapshot: int,
    top_k: int,
    pool_multiplier: int,
    zero_eps: float,
) -> tuple[str, dict[str, Any]]:
    row: dict[str, Any] = {
        "frame": int(slot),
        "snapshot_index": int(snapshot),
        "source": str(bundle.path),
        "orbit_phase": float(snapshot),
        "top_k": int(top_k),
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
        metrics = _triad_metrics(modes, zero_eps=zero_eps)
    except Exception as exc:  # noqa: BLE001
        row["status"] = ERROR_STATUS
        row["errors"] = [f"frame_orbit_phase_reconstruction_error: {exc}"]
        return ERROR_STATUS, row

    row.update(metrics)
    if int(metrics["triad_count"]) <= 0:
        row["status"] = PARTIAL_STATUS
        row["warnings"] = ["no resonant selected-mode triads found"]
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

    slots = _frame_indices(bundle.frame_count, args.frame, args.frame_limit)
    rows: list[dict[str, Any]] = []
    counts = {OK_STATUS: 0, PARTIAL_STATUS: 0, ERROR_STATUS: 0}
    for slot in slots:
        status, row = evaluate_frame_orbit_phase(
            bundle=bundle,
            slot=slot,
            snapshot=slot,
            top_k=args.top_k,
            pool_multiplier=args.pool_multiplier,
            zero_eps=float(args.zero_eps),
        )
        counts[status] = counts.get(status, 0) + 1
        rows.append(row)

    ok_rows = [row for row in rows if row.get("status") == OK_STATUS]
    agg = {
        "processed_frames": len(rows),
        "ok_frames": counts.get(OK_STATUS, 0),
        "partial_frames": counts.get(PARTIAL_STATUS, 0),
        "error_frames": counts.get(ERROR_STATUS, 0),
        "top_k": int(args.top_k),
        "orbit_coherence_mean": float(np.mean([row.get("orbit_coherence", 0.0) for row in ok_rows])) if ok_rows else 0.0,
        "phase_alignment_fraction_mean": float(np.mean([row.get("phase_alignment_fraction", 0.0) for row in ok_rows])) if ok_rows else 0.0,
        "constructive_weight_fraction_mean": float(np.mean([row.get("constructive_weight_fraction", 0.0) for row in ok_rows])) if ok_rows else 0.0,
        "phase_bias_mean": float(np.mean([row.get("phase_bias", 0.0) for row in ok_rows])) if ok_rows else 0.0,
        "orbit_phase_strength_mean": float(np.mean([row.get("orbit_phase_strength", 0.0) for row in ok_rows])) if ok_rows else 0.0,
        "mode_concentration_fraction_mean": float(np.mean([row.get("mode_concentration_fraction", 0.0) for row in ok_rows])) if ok_rows else 0.0,
        "coherence_vs_constructive_weight_correlation": _pearson(
            [float(row.get("orbit_coherence", 0.0)) for row in ok_rows],
            [float(row.get("constructive_weight_fraction", 0.0)) for row in ok_rows],
        ),
        "coherence_vs_concentration_correlation": _pearson(
            [float(row.get("orbit_coherence", 0.0)) for row in ok_rows],
            [float(row.get("mode_concentration_fraction", 0.0)) for row in ok_rows],
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
            "zero_eps": float(args.zero_eps),
            "frame": args.frame,
            "frame_limit": args.frame_limit,
        },
        "status": OK_STATUS if counts.get(ERROR_STATUS, 0) == 0 else PARTIAL_STATUS,
        "warnings": warnings,
        "errors": [],
        "aggregate": agg,
        "orbit_phase_rows": rows,
    }

    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(_json_text(payload, args.pretty) + "\n", encoding="utf-8")
    print(_json_text(payload, args.pretty))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
