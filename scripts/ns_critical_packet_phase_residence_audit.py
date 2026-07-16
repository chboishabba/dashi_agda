#!/usr/bin/env python3
"""Adversarial finite-data audit for dyadic critical-packet recurrence.

For the finite periodic snapshots in an NS archive this script measures

    X_j = 2^j sum_{2^j <= |k| < 2^(j+1)} |u_hat(k)|^2.

It then asks whether a shell which is both dominant and locally tight can
reappear after its nominal viscous time ``c * 2**(-2*j) / nu``.  Crucially,
every resolved packet observation is compared against the *exact heat
continuation of its observed spectrum*, rather than against a representative
shell wave number.  For archives declaring the generator's 2/3-dealiased
pseudospectral convention, it also reconstructs the nonlinear shell rate and
reports a saved-snapshot quadrature of the shell balance.  The result is a
falsification diagnostic for the proposed critical-packet residence barrier,
not a discretisation of a blow-up theorem:

* finite snapshots do not quantify over all smooth data;
* a nearest saved frame is not exactly the parabolic endpoint;
* a reconstructed saved-snapshot balance is not an exact identity of the
  solver's RK stages;
* the available cadence deliberately marks high shells as unresolved.

The phase rows are finite-difference helical-coordinate telemetry.  They are
included to find persistent coherent candidates, not to assert the exact
helical amplitude/phase ODE or a pressure-localisation theorem.
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any

import numpy as np


SCRIPT_NAME = "scripts/ns_critical_packet_phase_residence_audit.py"
DEFAULT_ARCHIVE = Path(
    "/home/c/Documents/code/dashiCFD/outputs/"
    "sprint65_pressure_reconstruction_N128_seed0_gpu/"
    "ns3d_N128_seed0_gpu_pressure.npz"
)
DEFAULT_OUTPUT = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_critical_packet_phase_residence_audit_N128_20260716.json"
)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--raw-archive", type=Path, default=DEFAULT_ARCHIVE)
    parser.add_argument("--output-json", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--c", type=float, default=1.0,
                        help="dimensionless multiple of the nominal viscous time")
    parser.add_argument("--critical-fraction", type=float, default=0.8,
                        help="X_j / max_l X_l needed for packet dominance")
    parser.add_argument("--tightness", type=float, default=0.8,
                        help="fraction of critical mass in shells j-1,j,j+1")
    parser.add_argument("--max-shell", type=int, default=6,
                        help="largest dyadic shell index included in the audit")
    parser.add_argument("--max-time-mismatch", type=float, default=0.5,
                        help="allow |observed-target| <= this * target time")
    parser.add_argument("--phase-sample-per-shell", type=int, default=64)
    return parser.parse_args()


def authority() -> dict[str, bool]:
    return {
        "candidate_only": True,
        "empirical_non_promoting": True,
        "theorem_authority": False,
        "clay_authority": False,
        "promoted": False,
    }


def load_archive(path: Path) -> tuple[np.ndarray, np.ndarray, float, float]:
    with np.load(path, allow_pickle=False) as data:
        velocity = np.asarray(data["velocity_snapshots"], dtype=np.float64)
        steps = np.asarray(data["steps"], dtype=np.int64)
        metadata = json.loads(str(np.asarray(data["meta_json"]).item()))
    if velocity.ndim != 5:
        raise ValueError(f"unsupported velocity_snapshots shape {velocity.shape!r}")
    if velocity.shape[-1] == 3:
        velocity = np.moveaxis(velocity, -1, 1)
    if velocity.shape[1] != 3:
        raise ValueError(f"cannot locate vector component axis in {velocity.shape!r}")
    dt = float(metadata["dt"])
    nu = float(metadata["nu0"])
    return velocity, steps, dt, nu


def frequency_grid(n: int) -> tuple[np.ndarray, np.ndarray]:
    """Return wavevectors in physical component order ``(x, y, z)``.

    Snapshots use spatial array order ``(z, y, x)`` and vector component order
    ``(x, y, z)``.  Keeping this distinction explicit matters for both Leray
    projection and the reconstructed convection term.
    """
    axis = np.fft.fftfreq(n) * n
    kz, ky, kx = np.meshgrid(axis, axis, axis, indexing="ij")
    norm = np.sqrt(kx * kx + ky * ky + kz * kz)
    return np.stack((kx, ky, kz), axis=0), norm


def leray_project(field_hat: np.ndarray, wave: np.ndarray, norm_sq: np.ndarray) -> np.ndarray:
    dot = np.sum(wave * field_hat, axis=0)
    projected = field_hat.copy()
    nonzero = norm_sq > 0.0
    for coordinate in range(3):
        correction = np.zeros_like(dot)
        correction[nonzero] = wave[coordinate][nonzero] * dot[nonzero] / norm_sq[nonzero]
        projected[coordinate] -= correction
    return projected


def dyadic_shell_packets(field_hat: np.ndarray, norm: np.ndarray, max_shell: int) -> np.ndarray:
    spectral_density = np.sum(np.abs(field_hat) ** 2, axis=0)
    packets = []
    for shell in range(max_shell + 1):
        lower = float(2 ** shell)
        upper = float(2 ** (shell + 1))
        mask = (norm >= lower) & (norm < upper)
        packets.append(float((2 ** shell) * np.sum(spectral_density[mask])))
    return np.asarray(packets, dtype=np.float64)


def component_dealias_mask(wave: np.ndarray, n: int) -> np.ndarray:
    """The generator's exact componentwise 2/3 retention convention."""
    cutoff = float(n) / 3.0
    return np.all(np.abs(wave) <= cutoff, axis=0)


def shell_dissipation(field_hat: np.ndarray, norm_sq: np.ndarray, norm: np.ndarray, max_shell: int) -> np.ndarray:
    """``D_j = 2^j sum_{k in S_j} |k|^2 |u_hat(k)|^2``."""
    spectral_density = np.sum(np.abs(field_hat) ** 2, axis=0)
    values = []
    for shell in range(max_shell + 1):
        lower = float(2 ** shell)
        upper = float(2 ** (shell + 1))
        mask = (norm >= lower) & (norm < upper)
        values.append(float((2 ** shell) * np.sum(norm_sq[mask] * spectral_density[mask])))
    return np.asarray(values, dtype=np.float64)


def heat_continued_packet(
    field_hat: np.ndarray, norm_sq: np.ndarray, norm: np.ndarray, shell: int, nu: float, delta_t: float,
) -> float:
    """Exact heat-semigroup packet value for the observed initial spectrum."""
    lower = float(2 ** shell)
    upper = float(2 ** (shell + 1))
    mask = (norm >= lower) & (norm < upper)
    spectral_density = np.sum(np.abs(field_hat) ** 2, axis=0)
    return float((2 ** shell) * np.sum(spectral_density[mask] * np.exp(-2.0 * nu * norm_sq[mask] * delta_t)))


def reconstructed_nonlinear_rhs(
    field_hat: np.ndarray, wave: np.ndarray, norm_sq: np.ndarray, dealias: np.ndarray,
) -> np.ndarray:
    """Reconstruct ``-P(u . grad u)`` using the archive's stated 2/3 rule.

    ``field_hat`` is stored in normalized coefficient convention and component
    first order.  This is a diagnostic reconstruction from saved fields, not a
    claim about the hidden RK substeps of the generator.
    """
    n = field_hat.shape[1]
    raw_hat = np.moveaxis(field_hat * float(n ** 3), 0, -1)
    velocity = np.fft.ifftn(raw_hat, axes=(0, 1, 2)).real
    gradient = np.empty(velocity.shape + (3,), dtype=np.float64)
    for component in range(3):
        for direction in range(3):
            gradient[..., component, direction] = np.fft.ifftn(
                1j * wave[direction] * raw_hat[..., component], axes=(0, 1, 2)
            ).real
    advection = np.empty_like(velocity)
    for component in range(3):
        advection[..., component] = sum(
            velocity[..., direction] * gradient[..., component, direction]
            for direction in range(3)
        )
    nonlinear_raw = -np.fft.fftn(advection, axes=(0, 1, 2))
    nonlinear_raw[~dealias, :] = 0.0
    dot = sum(wave[component] * nonlinear_raw[..., component] for component in range(3))
    nonzero = norm_sq > 0.0
    for component in range(3):
        correction = np.zeros_like(dot)
        correction[nonzero] = wave[component][nonzero] * dot[nonzero] / norm_sq[nonzero]
        nonlinear_raw[..., component] -= correction
    nonlinear_raw[0, 0, 0, :] = 0.0
    return np.moveaxis(nonlinear_raw / float(n ** 3), -1, 0)


def shell_nonlinear_rate(
    field_hat: np.ndarray, nonlinear_hat: np.ndarray, norm: np.ndarray, max_shell: int,
) -> np.ndarray:
    """``N_j = 2 * 2^j Re sum_{k in S_j} conj(u_hat) N_hat``."""
    values = []
    for shell in range(max_shell + 1):
        lower = float(2 ** shell)
        upper = float(2 ** (shell + 1))
        mask = (norm >= lower) & (norm < upper)
        pairing = np.sum(np.conjugate(field_hat[:, mask]) * nonlinear_hat[:, mask])
        values.append(float(2.0 * (2 ** shell) * np.real(pairing)))
    return np.asarray(values, dtype=np.float64)


def trapezoid_integral(times: np.ndarray, values: np.ndarray, start: int, end: int) -> float:
    if end <= start:
        return 0.0
    return float(np.trapezoid(values[start:end + 1], times[start:end + 1]))


def helical_basis(k: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    norm = float(np.linalg.norm(k))
    if norm == 0.0:
        raise ValueError("zero mode has no helical basis")
    khat = k / norm
    axis = np.eye(3)[int(np.argmin(np.abs(khat)))]
    e1 = np.cross(khat, axis)
    e1 /= np.linalg.norm(e1)
    e2 = np.cross(khat, e1)
    return ((e1 + 1j * e2) / math.sqrt(2.0),
            (e1 - 1j * e2) / math.sqrt(2.0))


def shell_mode_indices(norm: np.ndarray, shell: int, limit: int) -> np.ndarray:
    mask = (norm >= float(2 ** shell)) & (norm < float(2 ** (shell + 1)))
    indices = np.argwhere(mask)
    # Deterministic, frequency-lexicographic sample; the phase rows are only
    # telemetry and must not claim full-shell quantification.
    return indices[:limit]


def helical_phase_rows(
    fields: list[np.ndarray], wave: np.ndarray, norm: np.ndarray, times: np.ndarray,
    max_shell: int, sample_per_shell: int,
) -> list[dict[str, float]]:
    rows: list[dict[str, float]] = []
    for shell in range(max_shell + 1):
        for i, j, k in shell_mode_indices(norm, shell, sample_per_shell):
            mode = wave[:, i, j, k]
            h_plus, h_minus = helical_basis(mode)
            for helicity, basis in ((1, h_plus), (-1, h_minus)):
                component = np.asarray([np.vdot(basis, field[:, i, j, k]) for field in fields])
                amplitude = np.abs(component)
                phase = np.unwrap(np.angle(component))
                for frame in range(len(fields) - 1):
                    delta_t = float(times[frame + 1] - times[frame])
                    if delta_t <= 0.0:
                        continue
                    if max(amplitude[frame], amplitude[frame + 1]) <= 1.0e-30:
                        continue
                    rows.append({
                        "shell": shell,
                        "helicity": helicity,
                        "frame": frame,
                        "amplitude": float(amplitude[frame]),
                        "amplitude_rate_fd": float((amplitude[frame + 1] - amplitude[frame]) / delta_t),
                        "phase_rate_fd": float((phase[frame + 1] - phase[frame]) / delta_t),
                    })
    return rows


def aggregate_phase_rows(rows: list[dict[str, float]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for shell in sorted({int(row["shell"]) for row in rows}):
        selected = [row for row in rows if int(row["shell"]) == shell]
        phase_rates = np.asarray([abs(row["phase_rate_fd"]) for row in selected])
        amplitude_rates = np.asarray([abs(row["amplitude_rate_fd"]) for row in selected])
        result[str(shell)] = {
            "sample_count": len(selected),
            "median_abs_phase_rate_fd": float(np.median(phase_rates)) if len(selected) else math.nan,
            "p90_abs_phase_rate_fd": float(np.quantile(phase_rates, 0.9)) if len(selected) else math.nan,
            "median_abs_amplitude_rate_fd": float(np.median(amplitude_rates)) if len(selected) else math.nan,
        }
    return result


def main() -> None:
    args = parse_args()
    if not (args.c > 0.0 and 0.0 < args.critical_fraction <= 1.0 and 0.0 < args.tightness <= 1.0):
        raise ValueError("c must be positive and fraction/tightness must lie in (0, 1]")
    velocity, steps, dt, nu = load_archive(args.raw_archive)
    n = velocity.shape[2]
    if velocity.shape[2:] != (n, n, n):
        raise ValueError(f"expected cubic vector snapshots, got {velocity.shape!r}")
    wave, norm = frequency_grid(n)
    norm_sq = norm * norm
    dealias = component_dealias_mask(wave, n)
    fields: list[np.ndarray] = []
    packets: list[np.ndarray] = []
    dissipations: list[np.ndarray] = []
    nonlinear_rates: list[np.ndarray] = []
    for snapshot in velocity:
        field_hat = np.fft.fftn(snapshot, axes=(1, 2, 3)) / float(n ** 3)
        field_hat = leray_project(field_hat, wave, norm_sq)
        fields.append(field_hat)
        packets.append(dyadic_shell_packets(field_hat, norm, args.max_shell))
        dissipations.append(shell_dissipation(field_hat, norm_sq, norm, args.max_shell))
        nonlinear_hat = reconstructed_nonlinear_rhs(field_hat, wave, norm_sq, dealias)
        nonlinear_rates.append(shell_nonlinear_rate(field_hat, nonlinear_hat, norm, args.max_shell))
    packet_matrix = np.asarray(packets)
    dissipation_matrix = np.asarray(dissipations)
    nonlinear_rate_matrix = np.asarray(nonlinear_rates)
    times = steps.astype(np.float64) * dt
    frame_interval = float(np.median(np.diff(times))) if len(times) > 1 else math.nan

    recurrence_rows: list[dict[str, Any]] = []
    for frame in range(len(times)):
        total_critical_mass = float(np.sum(packet_matrix[frame]))
        shell_max = float(np.max(packet_matrix[frame]))
        for shell in range(args.max_shell + 1):
            x_initial = float(packet_matrix[frame, shell])
            neighbourhood = float(np.sum(packet_matrix[frame, max(0, shell - 1):min(args.max_shell + 1, shell + 2)]))
            dominance = x_initial / shell_max if shell_max > 0.0 else math.nan
            tightness = neighbourhood / total_critical_mass if total_critical_mass > 0.0 else math.nan
            target_delta = args.c * (2.0 ** (-2 * shell)) / nu
            target_time = float(times[frame] + target_delta)
            future = np.arange(frame + 1, len(times))
            if len(future) == 0 or x_initial <= 1.0e-30:
                continue
            nearest = int(future[np.argmin(np.abs(times[future] - target_time))])
            observed_delta = float(times[nearest] - times[frame])
            mismatch = abs(observed_delta - target_delta) / target_delta
            candidate = dominance >= args.critical_fraction and tightness >= args.tightness
            # A nearest *earlier* endpoint near the end of a finite trajectory
            # cannot witness recurrence over the requested parabolic window.
            # Requiring the whole target interval to be recorded prevents an
            # artificial short-time decay ratio from being reported as leakage.
            target_in_recorded_horizon = target_time <= float(times[-1])
            resolved = target_in_recorded_horizon and mismatch <= args.max_time_mismatch
            x_linear_final = heat_continued_packet(
                fields[frame], norm_sq, norm, shell, nu, observed_delta
            )
            linear_ratio = x_linear_final / x_initial
            recurrence_ratio = float(packet_matrix[nearest, shell] / x_initial)
            compensated_ratio = recurrence_ratio / linear_ratio if linear_ratio > 1.0e-30 else math.nan
            dissipation_integral = trapezoid_integral(times, dissipation_matrix[:, shell], frame, nearest)
            nonlinear_integral = trapezoid_integral(times, nonlinear_rate_matrix[:, shell], frame, nearest)
            balance_lhs = float(packet_matrix[nearest, shell] - x_initial + 2.0 * nu * dissipation_integral)
            balance_residual = balance_lhs - nonlinear_integral
            viscous_integral = 2.0 * nu * dissipation_integral
            replenishment_ratio = nonlinear_integral / viscous_integral if viscous_integral > 1.0e-30 else math.nan
            initial_viscous_rate = 2.0 * nu * float(dissipation_matrix[frame, shell])
            initial_nonlinear_rate = float(nonlinear_rate_matrix[frame, shell])
            recurrence_rows.append({
                "shell": shell,
                "frame_start": frame,
                "frame_end": nearest,
                "time_start": float(times[frame]),
                "time_end": float(times[nearest]),
                "target_parabolic_delta": target_delta,
                "observed_delta": observed_delta,
                "relative_time_mismatch": mismatch,
                "target_in_recorded_horizon": target_in_recorded_horizon,
                "resolved": resolved,
                "critical_packet_candidate": candidate,
                "x_initial": x_initial,
                "x_final": float(packet_matrix[nearest, shell]),
                "x_linear_final_exact_spectrum": x_linear_final,
                "linear_heat_ratio_exact_spectrum": linear_ratio,
                "recurrence_ratio": recurrence_ratio,
                "heat_compensated_ratio": compensated_ratio,
                "initial_nonlinear_to_viscous_ratio": (
                    abs(initial_nonlinear_rate) / initial_viscous_rate
                    if initial_viscous_rate > 1.0e-30 else math.nan
                ),
                "shell_balance_saved_snapshot": {
                    "nonlinear_integral": nonlinear_integral,
                    "viscous_integral": viscous_integral,
                    "replenishment_ratio": replenishment_ratio,
                    "balance_lhs": balance_lhs,
                    "balance_residual": balance_residual,
                    "relative_balance_residual": (
                        abs(balance_residual) / max(
                            abs(float(packet_matrix[nearest, shell] - x_initial)),
                            abs(viscous_integral), abs(nonlinear_integral), 1.0e-30,
                        )
                    ),
                },
                "dominance": dominance,
                "local_tightness": tightness,
            })

    resolved_candidates = [
        row for row in recurrence_rows
        if row["resolved"] and row["critical_packet_candidate"]
    ]
    candidate_summary: dict[str, Any]
    if resolved_candidates:
        ratios = np.asarray([row["recurrence_ratio"] for row in resolved_candidates])
        linear_ratios = np.asarray([row["linear_heat_ratio_exact_spectrum"] for row in resolved_candidates])
        compensated_ratios = np.asarray([row["heat_compensated_ratio"] for row in resolved_candidates])
        replenishments = np.asarray([
            row["shell_balance_saved_snapshot"]["replenishment_ratio"] for row in resolved_candidates
        ])
        candidate_summary = {
            "resolved_candidate_count": len(resolved_candidates),
            "max_recurrence_ratio": float(np.max(ratios)),
            "median_recurrence_ratio": float(np.median(ratios)),
            "max_linear_heat_ratio_exact_spectrum": float(np.max(linear_ratios)),
            "median_linear_heat_ratio_exact_spectrum": float(np.median(linear_ratios)),
            "max_heat_compensated_ratio": float(np.max(compensated_ratios)),
            "median_heat_compensated_ratio": float(np.median(compensated_ratios)),
            "max_saved_snapshot_replenishment_ratio": float(np.max(replenishments)),
            "median_saved_snapshot_replenishment_ratio": float(np.median(replenishments)),
            "growth_or_full_recurrence_observed": bool(np.any(ratios >= 1.0)),
            "nonlinear_replenishment_offsets_viscosity_observed": bool(np.any(replenishments >= 1.0)),
        }
    else:
        candidate_summary = {
            "resolved_candidate_count": 0,
            "growth_or_full_recurrence_observed": False,
            "decision": "no resolved dominant-tight packet in this finite decaying trajectory",
        }

    phase_rows = helical_phase_rows(fields, wave, norm, times, args.max_shell, args.phase_sample_per_shell)
    payload: dict[str, Any] = {
        "contract": "ns_critical_packet_phase_residence_audit",
        "authority": authority(),
        "status": "ok",
        "definition": {
            "critical_packet": "X_j = 2^j sum_{2^j <= |k| < 2^(j+1)} |u_hat(k)|^2",
            "candidate_condition": "X_j >= critical_fraction * max_l X_l and shells j-1,j,j+1 carry at least tightness of selected critical mass",
            "target_window": "c * 2^(-2j) / nu for the Fourier convention u_t + nu |k|^2 u = ...",
            "dynamic_rescaling": "X_j is already scale-invariant; recurrence_ratio is the sampled packet ratio",
            "heat_baseline": "X_j^lin(t0 + dt) = 2^j sum_{k in S_j} |u_hat(k,t0)|^2 exp(-2 nu |k|^2 dt)",
            "shell_balance": "X_j(t1)-X_j(t0)+2 nu integral D_j = integral N_j; integrals are trapezoid reconstructions from saved fields using the archive's stated 2/3-dealiased pseudospectral convention",
            "phase_telemetry": "finite-difference helical amplitudes/phases on a deterministic subsample, not the exact phase ODE",
        },
        "inputs": {
            "raw_archive": str(args.raw_archive),
            "frame_count": int(len(times)),
            "steps": [int(value) for value in steps],
            "times": [float(value) for value in times],
            "dt": dt,
            "snapshot_interval": frame_interval,
            "nu": nu,
            "c": args.c,
            "critical_fraction": args.critical_fraction,
            "tightness": args.tightness,
            "max_shell": args.max_shell,
            "max_time_mismatch": args.max_time_mismatch,
        },
        "packets": {
            "shell_indices": list(range(args.max_shell + 1)),
            "values_by_frame": [[float(value) for value in row] for row in packet_matrix],
        },
        "recurrence": {
            "rows": recurrence_rows,
            "candidate_summary": candidate_summary,
            "warning": "The heat-compensated ratio distinguishes observed packet survival from the exact heat continuation of its initial spectrum. A single smooth, unforced, decaying trajectory cannot establish a universal leakage constant; reconstructed saved-snapshot balances are not exact RK-stage identities.",
        },
        "phase_finite_difference_telemetry": {
            "row_count": len(phase_rows),
            "by_shell": aggregate_phase_rows(phase_rows),
            "warning": "Finite differences at snapshot cadence are diagnostic only; no exact helical ODE or phase-locking theorem is inferred.",
        },
        "decision": (
            "candidate-only adversarial recurrence audit; it neither proves nor refutes the universal "
            "critical-packet residence barrier, but can falsify it on observed resolved candidates."
        ),
    }
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(json.dumps(payload, indent=2, sort_keys=True, allow_nan=False) + "\n", encoding="utf-8")
    print(json.dumps(payload, indent=2, sort_keys=True, allow_nan=False))


if __name__ == "__main__":
    main()
