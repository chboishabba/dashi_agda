#!/usr/bin/env python3
"""Adversarial phase search for a finite NS critical-packet recurrence test.

This is intentionally a *counterexample search*, not evidence for a packet
barrier.  It builds a reality-symmetric, divergence-free donor-star network:
two-shell donor pairs ``p + q = -r`` share a target-shell mode ``r``.  Helical
phases are sampled under fixed amplitudes, target-packet dominance, and exact
Leray/dealias constraints.  The static stage ranks phase states by their
initial nonlinear replenishment of the target dyadic packet.

With ``--backend gpu`` or ``--backend cpu``, the selected candidates are then
evolved under the sibling dashiCFD finite Galerkin solver and ranked by the
actual endpoint objective ``X_j(T) / X_j(0)``.  This can falsify a proposed
uniform contraction in the tested finite family; it cannot prove a universal
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
    parser.add_argument("--target-shell", type=int, default=3)
    parser.add_argument("--window-c", type=float, default=1.0)
    parser.add_argument("--phase-samples", type=int, default=256)
    parser.add_argument("--seed", type=int, default=20260716)
    parser.add_argument("--target-amplitude", type=float, default=3.0)
    parser.add_argument("--donor-amplitude", type=float, default=1.0)
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


def build_candidate(args: argparse.Namespace, phases: np.ndarray) -> np.ndarray:
    target, donors = donor_star_modes()
    if len(phases) != len(donors):
        raise ValueError("one phase is required per donor pair")
    raw_hat = np.zeros((args.n, args.n, args.n, 3), dtype=np.complex128)
    add_reality_symmetric_helical_mode(raw_hat, target, args.target_amplitude, 0.0, 1)
    for phase, donor in zip(phases, donors, strict=True):
        partner = tuple(-target[index] - donor[index] for index in range(3))
        # The pair shares a single phase sum while retaining deterministic,
        # non-identical individual phases.  Alternate helicity keeps the
        # search from hard-wiring a homochiral-only mechanism.
        add_reality_symmetric_helical_mode(raw_hat, donor, args.donor_amplitude, float(phase), 1)
        add_reality_symmetric_helical_mode(raw_hat, partner, args.donor_amplitude, float(-0.37 * phase), -1)
    return normalise_urms(raw_hat, args.target_urms)


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


def evolve_candidate(args: argparse.Namespace, raw_hat: np.ndarray, wave: np.ndarray, norm: np.ndarray, norm_sq: np.ndarray) -> dict[str, Any]:
    """Evolve one phase candidate and return endpoint packet/heat diagnostics."""
    module = load_cfd_module(args)
    target_time = args.window_c * (2.0 ** (-2 * args.target_shell)) / args.nu
    steps = int(math.ceil(target_time / args.dt))
    actual_time = steps * args.dt
    _, kx, ky, kz, k2, _ = module.make_grid(args.n, 2.0 * math.pi)
    mask = module.component_dealias_mask(kx, ky, kz, args.n, 2.0 * math.pi)
    initial_field = raw_to_field_hat(raw_hat, wave, norm_sq)
    initial_packet = float(dyadic_shell_packets(initial_field, norm, args.target_shell)[args.target_shell])
    heat_packet = heat_continued_packet(
        initial_field, norm_sq, norm, args.target_shell, args.nu, actual_time
    )
    history: list[dict[str, float]] = []
    if args.backend == "gpu":
        from vulkan_truth3d_backend import VulkanTruth3DBackend
        backend = VulkanTruth3DBackend(args.n, dt=args.dt, nu0=args.nu, length=2.0 * math.pi, fft_backend=args.fft_backend)
        try:
            backend.set_initial_u_hat(raw_hat)
            for step in range(steps + 1):
                if step % args.save_every == 0 or step == steps:
                    current_raw = np.asarray(backend.read_u_hat(), dtype=np.complex128)
                    current_field = raw_to_field_hat(current_raw, wave, norm_sq)
                    current_packet = float(dyadic_shell_packets(current_field, norm, args.target_shell)[args.target_shell])
                    history.append({"step": step, "time": step * args.dt, "target_packet": current_packet})
                if step < steps:
                    backend.step()
        finally:
            backend.close()
    else:
        current_raw = raw_hat.copy()
        for step in range(steps + 1):
            if step % args.save_every == 0 or step == steps:
                current_field = raw_to_field_hat(current_raw, wave, norm_sq)
                current_packet = float(dyadic_shell_packets(current_field, norm, args.target_shell)[args.target_shell])
                history.append({"step": step, "time": step * args.dt, "target_packet": current_packet})
            if step < steps:
                current_raw = module.rk2_step(current_raw, kx, ky, kz, k2, mask, args.dt, args.nu)
    final_packet = float(history[-1]["target_packet"])
    return {
        "steps": steps,
        "target_time": target_time,
        "actual_time": actual_time,
        "initial_packet": initial_packet,
        "heat_only_packet_exact_spectrum": heat_packet,
        "final_packet": final_packet,
        "endpoint_recurrence_ratio": final_packet / initial_packet,
        "endpoint_heat_compensated_ratio": final_packet / heat_packet if heat_packet > 1.0e-30 else math.nan,
        "history": history,
    }


def main() -> None:
    args = parse_args()
    if args.n < 24 or args.nu <= 0.0 or args.dt <= 0.0 or args.phase_samples <= 0:
        raise ValueError("n >= 24, nu/dt > 0, and phase-samples > 0 are required")
    if args.target_shell != 3 or args.n != 32:
        raise ValueError("the current explicit donor-star topology is defined only for N32 target shell j=3")
    wave, norm = frequency_grid(args.n)
    norm_sq = norm * norm
    rng = np.random.default_rng(args.seed)
    candidates: list[dict[str, Any]] = []
    for sample in range(args.phase_samples):
        phases = rng.uniform(-math.pi, math.pi, size=4)
        raw_hat = build_candidate(args, phases)
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
                "endpoint": evolve_candidate(args, build_candidate(args, np.asarray(candidate["phases"])), wave, norm, norm_sq),
                "elapsed_seconds": time.perf_counter() - started,
            })
    payload = {
        "contract": "ns_phase_locked_packet_adversarial_search",
        "authority": authority(),
        "status": "ok",
        "topology": {
            "kind": "shared-target adjacent-shell donor star",
            "target_mode": donor_star_modes()[0],
            "donor_modes": donor_star_modes()[1],
            "constraints": "reality symmetric, divergence free helical modes, componentwise 2/3 dealiased N32 support, fixed amplitudes and target urms",
        },
        "objective": {
            "static_prefilter": "maximize initial nonlinear target-shell inflow",
            "endpoint": "maximize X_j(T) / X_j(0) at T = c * 2^(-2j) / nu",
            "warning": "static inflow is not a substitute for endpoint recurrence; endpoint rows are present only when --backend is not none",
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
