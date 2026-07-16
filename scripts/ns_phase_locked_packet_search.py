#!/usr/bin/env python3
"""Adversarial phase search for finite NS critical-packet recurrence.

This is intentionally a *counterexample search*, not evidence for a packet
barrier.  It builds reality-symmetric, divergence-free helical networks.  The
default is a three-target cyclic feedback graph:

    lower donors -> r_i -> s_i -> r_(i+1).

The ``s_i`` modes are shared by outlet and feedback triads, so their phases
cannot independently maximize every transfer.

With ``--backend gpu`` or ``--backend cpu``, the selected candidates are then
evolved under the sibling dashiCFD finite Galerkin solver and ranked by the
actual multi-window endpoint objective.  This can falsify a proposed uniform
contraction in the tested finite family; it cannot prove a universal
Navier--Stokes theorem.
"""

from __future__ import annotations

import argparse
import importlib.util
import json
import math
import sys
import time
from pathlib import Path
from typing import Any

import numpy as np

from ns_critical_packet_phase_residence_audit import (
    component_dealias_mask,
    dyadic_shell_packets,
    frequency_grid,
    heat_continued_packet,
    leray_project,
    reconstructed_nonlinear_rhs,
    shell_dissipation,
    shell_nonlinear_rate,
)
from ns_triad_edge_depletion_audit import helical_basis


SCRIPT_NAME = "scripts/ns_phase_locked_packet_search.py"
DEFAULT_CFD_ROOT = Path("/home/c/Documents/code/dashiCFD")
DEFAULT_OUTPUT = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_phase_locked_packet_search_N32_20260716.json"
)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--n", type=int, default=32)
    parser.add_argument("--nu", type=float, default=1.0e-3)
    parser.add_argument("--dt", type=float, default=1.0e-3)
    parser.add_argument("--target-shell", type=int, default=2)
    parser.add_argument("--window-c", type=float, default=1.0)
    parser.add_argument("--windows", type=int, default=2,
                        help="complete viscous windows in the endpoint objective")
    parser.add_argument("--topology", choices=("cyclic-feedback", "donor-star"),
                        default="cyclic-feedback")
    parser.add_argument("--phase-samples", type=int, default=256)
    parser.add_argument("--seed", type=int, default=20260716)
    parser.add_argument("--target-amplitude", type=float, default=3.0)
    parser.add_argument("--donor-amplitude", type=float, default=1.0)
    parser.add_argument("--feedback-amplitude", type=float, default=1.0)
    parser.add_argument("--normalization", choices=("critical", "urms"), default="critical",
                        help="fix total finite H^(1/2) packet mass or physical-space urms")
    parser.add_argument("--critical-mass", type=float, default=1.0,
                        help="sum_j X_j imposed when --normalization critical")
    parser.add_argument("--target-urms", type=float, default=1.0)
    parser.add_argument("--top-candidates", type=int, default=1)
    parser.add_argument("--backend", choices=("none", "cpu", "gpu"), default="none")
    parser.add_argument("--fft-backend", default="vkfft-vulkan")
    parser.add_argument("--save-every", type=int, default=100)
    parser.add_argument("--cfd-root", type=Path, default=DEFAULT_CFD_ROOT)
    parser.add_argument("--output-json", type=Path, default=DEFAULT_OUTPUT)
    return parser.parse_args()


def authority() -> dict[str, bool]:
    return {
        "candidate_only": True,
        "empirical_non_promoting": True,
        "theorem_authority": False,
        "clay_authority": False,
        "promoted": False,
    }


def mode_index(mode: tuple[int, int, int], n: int) -> tuple[int, int, int]:
    """Physical mode ``(kx, ky, kz)`` to archive array order ``(z, y, x)``."""
    kx, ky, kz = mode
    return kz % n, ky % n, kx % n


def negate(mode: tuple[int, int, int]) -> tuple[int, int, int]:
    return tuple(-value for value in mode)


def donor_star_modes() -> tuple[tuple[int, int, int], list[tuple[int, int, int]]]:
    """A shared-target adjacent-shell donor star, all within N32 2/3 support."""
    target = (-8, 0, 0)
    donors = [(4, 3, 0), (4, 0, 3), (4, 3, 3), (4, 2, 4)]
    return target, donors


def network_spec(args: argparse.Namespace) -> dict[str, Any]:
    """Return an explicit finite graph in physical wavevector coordinates.

    The feedback graph is placed at ``N=32, j=2``.  Its targets have size
    four; the shared outlet/feedback modes have size above eight, while every
    coordinate remains in the componentwise 2/3-dealiased carrier.
    """
    if args.topology == "donor-star":
        target, donors = donor_star_modes()
        entries: list[dict[str, Any]] = [{
            "mode": target, "amplitude": args.target_amplitude, "helicity": 1,
            "fixed_phase": 0.0, "role": "target",
        }]
        triads: list[dict[str, Any]] = []
        for index, donor in enumerate(donors):
            partner = tuple(-target[axis] - donor[axis] for axis in range(3))
            entries.extend((
                {"mode": donor, "amplitude": args.donor_amplitude, "helicity": 1,
                 "role": f"donor-{index}"},
                {"mode": partner, "amplitude": args.donor_amplitude, "helicity": -1,
                 "role": f"donor-partner-{index}"},
            ))
            triads.append({"kind": "lower-donor", "modes": [donor, partner, target]})
        return {"kind": "shared-target adjacent-shell donor star", "targets": [target],
                "entries": entries, "triads": triads}

    targets = [(4, 0, 0), (0, 4, 0), (0, 0, 4)]
    donors = [
        [(-2, 1, 0), (-2, -1, 0)],
        [(1, -2, 0), (-1, -2, 0)],
        [(1, 0, -2), (-1, 0, -2)],
    ]
    # r_i + a_i + s_i = 0 and s_i + b_i + r_(i+1) = 0, cyclically.
    feedback = [
        {"a": (-10, -6, 0), "s": (6, 6, 0), "b": (-6, -10, 0)},
        {"a": (0, -10, -6), "s": (0, 6, 6), "b": (0, -6, -10)},
        {"a": (-6, 0, -10), "s": (6, 0, 6), "b": (-10, 0, -6)},
    ]
    entries: list[dict[str, Any]] = [
        {"mode": target, "amplitude": args.target_amplitude, "helicity": 1,
         "fixed_phase": 0.0, "role": f"target-{index}"}
        for index, target in enumerate(targets)
    ]
    triads: list[dict[str, Any]] = []
    for index, (target, pair, link) in enumerate(zip(targets, donors, feedback, strict=True)):
        for local, mode in enumerate(pair):
            entries.append({"mode": mode, "amplitude": args.donor_amplitude,
                            "helicity": 1 if local == 0 else -1,
                            "role": f"donor-{index}-{local}"})
        entries.extend((
            {"mode": link["a"], "amplitude": args.feedback_amplitude, "helicity": -1,
             "role": f"outlet-side-{index}"},
            {"mode": link["s"], "amplitude": args.feedback_amplitude, "helicity": 1,
             "role": f"shared-outlet-{index}"},
            {"mode": link["b"], "amplitude": args.feedback_amplitude, "helicity": -1,
             "role": f"feedback-{index}"},
        ))
        triads.extend((
            {"kind": "lower-donor", "modes": [pair[0], pair[1], target]},
            {"kind": "upper-outlet", "modes": [target, link["a"], link["s"]]},
            {"kind": "feedback", "modes": [link["s"], link["b"], targets[(index + 1) % len(targets)]]},
        ))
    return {"kind": "three-target cyclic outlet-feedback graph", "targets": targets,
            "entries": entries, "triads": triads}


def validate_network(args: argparse.Namespace, network: dict[str, Any]) -> None:
    if args.n != 32:
        raise ValueError("the explicit experimental networks are currently calibrated only for N32")
    expected_shell = 3 if args.topology == "donor-star" else 2
    if args.target_shell != expected_shell:
        raise ValueError(f"{args.topology} requires --target-shell {expected_shell}")
    cutoff = args.n / 3.0
    for entry in network["entries"]:
        if max(abs(value) for value in entry["mode"]) > cutoff:
            raise ValueError(f"network mode escapes 2/3 carrier: {entry['mode']!r}")
    for triad in network["triads"]:
        total = tuple(sum(mode[axis] for mode in triad["modes"]) for axis in range(3))
        if total != (0, 0, 0):
            raise ValueError(f"invalid zero-sum network triad: {triad!r}")


def add_reality_symmetric_helical_mode(
    raw_hat: np.ndarray, mode: tuple[int, int, int], amplitude: float, phase: float, helicity: int,
) -> None:
    """Insert one mode and its conjugate exactly in physical component order."""
    basis = helical_basis(mode)[0 if helicity > 0 else 1]
    coefficient = amplitude * np.exp(1j * phase) * basis
    raw_hat[mode_index(mode, raw_hat.shape[0])] += coefficient
    raw_hat[mode_index(negate(mode), raw_hat.shape[0])] += np.conjugate(coefficient)


def normalise_urms(raw_hat: np.ndarray, target_urms: float) -> np.ndarray:
    velocity = np.fft.ifftn(raw_hat, axes=(0, 1, 2)).real
    urms = float(np.sqrt(np.mean(np.sum(velocity * velocity, axis=-1))))
    if urms <= 1.0e-30:
        raise ValueError("phase candidate has zero velocity")
    return raw_hat * (target_urms / urms)


def normalise_critical_mass(raw_hat: np.ndarray, critical_mass: float) -> np.ndarray:
    """Set ``sum_j 2^j ||P_j u||_2^2`` to one common finite-carrier scale."""
    _, norm = frequency_grid(raw_hat.shape[0])
    field_hat = np.moveaxis(raw_hat / float(raw_hat.shape[0] ** 3), -1, 0)
    max_shell = int(math.ceil(math.log2(float(np.max(norm)) + 1.0)))
    observed_mass = float(np.sum(dyadic_shell_packets(field_hat, norm, max_shell)))
    if observed_mass <= 1.0e-30:
        raise ValueError("phase candidate has zero critical packet mass")
    return raw_hat * math.sqrt(critical_mass / observed_mass)


def build_candidate(args: argparse.Namespace, network: dict[str, Any], phases: np.ndarray) -> np.ndarray:
    variable_entries = [entry for entry in network["entries"] if "fixed_phase" not in entry]
    if len(phases) != len(variable_entries):
        raise ValueError("one phase is required per non-fixed network mode")
    raw_hat = np.zeros((args.n, args.n, args.n, 3), dtype=np.complex128)
    phase_iter = iter(float(phase) for phase in phases)
    for entry in network["entries"]:
        phase = float(entry["fixed_phase"]) if "fixed_phase" in entry else next(phase_iter)
        add_reality_symmetric_helical_mode(
            raw_hat, entry["mode"], float(entry["amplitude"]), phase, int(entry["helicity"])
        )
    return (normalise_critical_mass(raw_hat, args.critical_mass)
            if args.normalization == "critical" else normalise_urms(raw_hat, args.target_urms))


def raw_to_field_hat(raw_hat: np.ndarray, wave: np.ndarray, norm_sq: np.ndarray) -> np.ndarray:
    n = raw_hat.shape[0]
    return leray_project(np.moveaxis(raw_hat / float(n ** 3), -1, 0), wave, norm_sq)


def static_metrics(args: argparse.Namespace, raw_hat: np.ndarray, wave: np.ndarray, norm: np.ndarray, norm_sq: np.ndarray) -> dict[str, float]:
    field_hat = raw_to_field_hat(raw_hat, wave, norm_sq)
    dealias = component_dealias_mask(wave, args.n)
    nonlinear_hat = reconstructed_nonlinear_rhs(field_hat, wave, norm_sq, dealias)
    packets = dyadic_shell_packets(field_hat, norm, args.target_shell)
    dissipations = shell_dissipation(field_hat, norm_sq, norm, args.target_shell)
    nonlinear_rates = shell_nonlinear_rate(field_hat, nonlinear_hat, norm, args.target_shell)
    target_packet = float(packets[args.target_shell])
    target_dissipation = float(dissipations[args.target_shell])
    target_nonlinear = float(nonlinear_rates[args.target_shell])
    total_packet = float(np.sum(packets))
    lower = max(0, args.target_shell - 1)
    upper = min(len(packets), args.target_shell + 2)
    return {
        "target_packet": target_packet,
        "target_packet_dominance": target_packet / float(np.max(packets)) if np.max(packets) > 0.0 else math.nan,
        "target_packet_local_tightness": float(np.sum(packets[lower:upper])) / total_packet if total_packet > 0.0 else math.nan,
        "target_nonlinear_rate": target_nonlinear,
        "target_viscous_rate": 2.0 * args.nu * target_dissipation,
        "initial_replenishment_ratio": target_nonlinear / (2.0 * args.nu * target_dissipation) if target_dissipation > 1.0e-30 else math.nan,
    }


def packet_shape_metrics(
    args: argparse.Namespace,
    field_hat: np.ndarray,
    norm: np.ndarray,
    network: dict[str, Any],
    reference_network_vector: np.ndarray | None,
) -> dict[str, float]:
    """Packet and designed-network telemetry at one exact solver checkpoint.

    ``network_correlation_direct`` does not quotient translations or lattice
    rotations.  It is a conservative first recurrence score; a symmetry-
    reduced relative-periodic-orbit search would be a later, stronger audit.
    """
    packets = dyadic_shell_packets(field_hat, norm, args.target_shell)
    target = float(packets[args.target_shell])
    lower = max(0, args.target_shell - 1)
    upper = min(len(packets), args.target_shell + 2)
    total = float(np.sum(packets))
    coordinates: list[np.ndarray] = []
    support_energy = 0.0
    all_energy = float(np.sum(np.abs(field_hat) ** 2))
    for entry in network["entries"]:
        for mode in (entry["mode"], negate(entry["mode"])):
            value = np.asarray(field_hat[(slice(None),) + mode_index(mode, args.n)], dtype=np.complex128)
            coordinates.append(value)
            support_energy += float(np.sum(np.abs(value) ** 2))
    vector = np.concatenate(coordinates)
    vector_norm = float(np.linalg.norm(vector))
    if reference_network_vector is None:
        correlation = 1.0
    else:
        reference_norm = float(np.linalg.norm(reference_network_vector))
        correlation = (float(abs(np.vdot(reference_network_vector, vector)) / (reference_norm * vector_norm))
                       if reference_norm > 1.0e-30 and vector_norm > 1.0e-30 else math.nan)
    return {
        "target_packet": target,
        "target_packet_dominance": target / float(np.max(packets)) if np.max(packets) > 0.0 else math.nan,
        "target_packet_local_tightness": float(np.sum(packets[lower:upper])) / total if total > 0.0 else math.nan,
        "designed_network_energy_fraction": support_energy / all_energy if all_energy > 1.0e-30 else math.nan,
        "support_leakage_fraction": 1.0 - support_energy / all_energy if all_energy > 1.0e-30 else math.nan,
        "network_correlation_direct": correlation,
        "_network_vector": vector,
    }


def load_cfd_module(args: argparse.Namespace) -> Any:
    scripts_dir = args.cfd_root / "scripts"
    if not scripts_dir.is_dir():
        raise FileNotFoundError(f"missing dashiCFD scripts directory: {scripts_dir}")
    sys.path.insert(0, str(scripts_dir))
    spec = importlib.util.spec_from_file_location("dashi_make_truth_3d", scripts_dir / "make_truth_3d.py")
    if spec is None or spec.loader is None:
        raise RuntimeError("could not load sibling finite-Galerkin solver")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def evolve_candidate(
    args: argparse.Namespace, network: dict[str, Any], raw_hat: np.ndarray,
    wave: np.ndarray, norm: np.ndarray, norm_sq: np.ndarray,
) -> dict[str, Any]:
    """Evolve one candidate and score every complete viscous-time window."""
    module = load_cfd_module(args)
    nominal_window_time = args.window_c * (2.0 ** (-2 * args.target_shell)) / args.nu
    window_steps = int(math.ceil(nominal_window_time / args.dt))
    actual_window_time = window_steps * args.dt
    steps = args.windows * window_steps
    actual_time = steps * args.dt
    _, kx, ky, kz, k2, _ = module.make_grid(args.n, 2.0 * math.pi)
    mask = module.component_dealias_mask(kx, ky, kz, args.n, 2.0 * math.pi)
    initial_field = raw_to_field_hat(raw_hat, wave, norm_sq)
    initial_shape = packet_shape_metrics(args, initial_field, norm, network, None)
    reference_network_vector = initial_shape.pop("_network_vector")
    initial_packet = float(initial_shape["target_packet"])
    heat_packets = [heat_continued_packet(
        initial_field, norm_sq, norm, args.target_shell, args.nu, window * actual_window_time
    ) for window in range(args.windows + 1)]
    history: list[dict[str, float]] = []

    def record(step: int, current_raw: np.ndarray) -> None:
        current_field = raw_to_field_hat(current_raw, wave, norm_sq)
        shape = packet_shape_metrics(args, current_field, norm, network, reference_network_vector)
        shape.pop("_network_vector")
        nonlinear = reconstructed_nonlinear_rhs(current_field, wave, norm_sq, component_dealias_mask(wave, args.n))
        dissipation = shell_dissipation(current_field, norm_sq, norm, args.target_shell)[args.target_shell]
        nonlinear_rate = shell_nonlinear_rate(current_field, nonlinear, norm, args.target_shell)[args.target_shell]
        history.append({"step": step, "time": step * args.dt, **shape,
                        "target_dissipation": float(dissipation),
                        "target_nonlinear_rate": float(nonlinear_rate)})

    if args.backend == "gpu":
        from vulkan_truth3d_backend import VulkanTruth3DBackend
        backend = VulkanTruth3DBackend(args.n, dt=args.dt, nu0=args.nu, length=2.0 * math.pi, fft_backend=args.fft_backend)
        try:
            backend.set_initial_u_hat(raw_hat)
            for step in range(steps + 1):
                if step % args.save_every == 0 or step % window_steps == 0 or step == steps:
                    record(step, np.asarray(backend.read_u_hat(), dtype=np.complex128))
                if step < steps:
                    backend.step()
        finally:
            backend.close()
    else:
        current_raw = raw_hat.copy()
        for step in range(steps + 1):
            if step % args.save_every == 0 or step % window_steps == 0 or step == steps:
                record(step, current_raw)
            if step < steps:
                current_raw = module.rk2_step(current_raw, kx, ky, kz, k2, mask, args.dt, args.nu)
    window_rows = [row for row in history if int(row["step"]) % window_steps == 0]
    ratios = [float(window_rows[index + 1]["target_packet"] / window_rows[index]["target_packet"])
              for index in range(len(window_rows) - 1)]
    log_score = float(np.mean(np.log(ratios))) if ratios and all(value > 0.0 for value in ratios) else math.nan
    times = np.asarray([row["time"] for row in history], dtype=np.float64)
    nonlinear_rates = np.asarray([row["target_nonlinear_rate"] for row in history], dtype=np.float64)
    dissipations = np.asarray([row["target_dissipation"] for row in history], dtype=np.float64)
    viscous_loss = float(2.0 * args.nu * np.trapezoid(dissipations, times))
    nonlinear_positive = float(np.trapezoid(np.maximum(nonlinear_rates, 0.0), times))
    nonlinear_negative = float(-np.trapezoid(np.minimum(nonlinear_rates, 0.0), times))
    final_packet = float(window_rows[-1]["target_packet"])
    return {
        "steps": steps,
        "nominal_window_time": nominal_window_time,
        "actual_window_time": actual_window_time,
        "windows": args.windows,
        "actual_time": actual_time,
        "initial_packet": initial_packet,
        "heat_only_packets_exact_spectrum": heat_packets,
        "final_packet": final_packet,
        "endpoint_recurrence_ratio": final_packet / initial_packet,
        "endpoint_heat_compensated_ratio": final_packet / heat_packets[-1] if heat_packets[-1] > 1.0e-30 else math.nan,
        "window_recurrence_ratios": ratios,
        "min_window_recurrence_ratio": min(ratios) if ratios else math.nan,
        "mean_log_window_recurrence": log_score,
        "nonlinear_positive_over_viscous_loss": nonlinear_positive / viscous_loss if viscous_loss > 1.0e-30 else math.nan,
        "nonlinear_negative_over_viscous_loss": nonlinear_negative / viscous_loss if viscous_loss > 1.0e-30 else math.nan,
        "window_checkpoints": window_rows,
        "history": history,
    }


def main() -> None:
    args = parse_args()
    if (args.n < 24 or args.nu <= 0.0 or args.dt <= 0.0 or args.phase_samples <= 0
            or args.windows <= 0 or args.top_candidates <= 0):
        raise ValueError("n >= 24, positive nu/dt/windows/candidates, and phase-samples > 0 are required")
    if args.critical_mass <= 0.0 or args.target_urms <= 0.0:
        raise ValueError("critical-mass and target-urms must be positive")
    network = network_spec(args)
    validate_network(args, network)
    variable_dimension = sum("fixed_phase" not in entry for entry in network["entries"])
    wave, norm = frequency_grid(args.n)
    norm_sq = norm * norm
    rng = np.random.default_rng(args.seed)
    candidates: list[dict[str, Any]] = []
    for sample in range(args.phase_samples):
        phases = rng.uniform(-math.pi, math.pi, size=variable_dimension)
        raw_hat = build_candidate(args, network, phases)
        metrics = static_metrics(args, raw_hat, wave, norm, norm_sq)
        candidates.append({"sample": sample, "phases": [float(value) for value in phases], **metrics})
    # Positive nonlinear inflow into the target shell is the inexpensive
    # phase-only prefilter.  Endpoint recurrence remains authoritative when
    # an evolution backend is requested.
    candidates.sort(key=lambda row: float(row["target_nonlinear_rate"]), reverse=True)
    selected = candidates[:args.top_candidates]
    endpoint_rows: list[dict[str, Any]] = []
    if args.backend != "none":
        for rank, candidate in enumerate(selected):
            started = time.perf_counter()
            endpoint_rows.append({
                "rank_by_initial_inflow": rank,
                "sample": candidate["sample"],
                "phases": candidate["phases"],
                "static": {key: value for key, value in candidate.items() if key not in {"sample", "phases"}},
                "endpoint": evolve_candidate(
                    args, network, build_candidate(args, network, np.asarray(candidate["phases"])), wave, norm, norm_sq
                ),
                "elapsed_seconds": time.perf_counter() - started,
            })
        endpoint_rows.sort(key=lambda row: float(row["endpoint"]["min_window_recurrence_ratio"]), reverse=True)
    payload = {
        "contract": "ns_phase_locked_packet_adversarial_search",
        "authority": authority(),
        "status": "ok",
        "topology": network | {
            "phase_dimension": variable_dimension,
            "constraints": "reality symmetric, divergence free helical modes, componentwise 2/3 dealiased N32 support, fixed amplitudes and declared global normalization",
        },
        "objective": {
            "static_prefilter": "maximize initial nonlinear target-shell inflow only to seed an endpoint search",
            "endpoint": "maximize min_m X_j((m+1)T) / X_j(mT), T = c * 2^(-2j) / nu",
            "secondary_endpoint": "maximize mean log window recurrence",
            "warning": "this version samples phase candidates and evolves only the prefiltered subset; it is not global endpoint optimization",
        },
        "inputs": vars(args) | {"cfd_root": str(args.cfd_root), "output_json": str(args.output_json)},
        "static_candidates_ranked": candidates,
        "endpoint_evolutions": endpoint_rows,
        "decision": "candidate-only adversarial search; any apparent recurrence is a finite numerical lead requiring independent reproduction, not a Navier--Stokes theorem.",
    }
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(json.dumps(payload, indent=2, sort_keys=True, allow_nan=False) + "\n", encoding="utf-8")
    print(json.dumps(payload, indent=2, sort_keys=True, allow_nan=False))


if __name__ == "__main__":
    main()
