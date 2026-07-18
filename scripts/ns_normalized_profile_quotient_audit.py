#!/usr/bin/env python3
"""Non-promoting audit of normalized finite NS profile shapes.

This is the first post-scale-copy experiment.  It creates finite,
reality-symmetric, divergence-free Fourier fields whose *shape* is varied by
angular width, radial width, helical mixture, and phase coherence.  Each trial
is normalised to one declared finite H^(1/2) mass.  The nonlinear-to-viscous
ratio chi is then matched by rejection across deterministic phase trials; it
is deliberately not silently changed by a second scalar normalisation.

For the selected target outputs the script also estimates the unsigned
convolution interaction measure by geometry strata.  The estimator is
Horvitz--Thompson-equivalent: it samples uniformly inside each finite stratum,
reports its population size and sample variance, and combines independent
stratum estimates.  It is an empirical receipt, not a theorem, a confidence
interval, or a Navier--Stokes regularity claim.
"""

from __future__ import annotations

import argparse
import importlib.util
import json
import math
import os
from collections import defaultdict
from pathlib import Path
import sys
import tempfile
from typing import Any

import numpy as np

from ns_critical_packet_phase_residence_audit import (
    component_dealias_mask,
    dyadic_shell_packets,
    frequency_grid,
    leray_project,
    reconstructed_nonlinear_rhs,
    shell_dissipation,
    shell_nonlinear_rate,
)
from ns_triad_edge_depletion_audit import helical_basis


SCRIPT_NAME = "scripts/ns_normalized_profile_quotient_audit.py"
DEFAULT_OUTPUT = Path("scripts/data/outputs/ns_interaction_closure_production/ns_normalized_profile_audit.json")
DEFAULT_CFD_ROOT = Path("/home/c/Documents/code/dashiCFD")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--n", type=int, default=32)
    parser.add_argument("--nu", type=float, default=1.0e-3)
    parser.add_argument("--target-shell", type=int, default=2)
    parser.add_argument("--critical-mass", type=float, default=1.0)
    parser.add_argument("--angular-width", type=float, default=1.2,
                        help="Gaussian angular width in radians; small values are cap-concentrated")
    parser.add_argument("--radial-log-width", type=float, default=0.42,
                        help="Gaussian width of log(|k|/2**target-shell)")
    parser.add_argument("--helicity-bias", type=float, default=0.0,
                        help="minus/plus energy imbalance in [-1, 1]")
    parser.add_argument("--spatial-coherence", type=float, default=0.0,
                        help="0=random modal phases, 1=phase-coherent origin-centred field")
    parser.add_argument("--angular-axis", type=float, nargs=3, default=(1.0, 0.0, 0.0))
    parser.add_argument("--seed", type=int, default=20260717)
    parser.add_argument("--chi-target", type=float, default=None,
                        help="target-shell nonlinear/viscous ratio in the selected --chi-sign convention")
    parser.add_argument("--chi-sign", choices=("absolute", "positive", "negative"), default="absolute",
                        help="absolute is calibration-only; positive/negative preserve signed nonlinear direction")
    parser.add_argument("--chi-attempts", type=int, default=8)
    parser.add_argument("--chi-tolerance", type=float, default=0.05)
    parser.add_argument("--require-chi-tolerance", action="store_true",
                        help="reject a candidate unless --chi-target is met within --chi-tolerance")
    parser.add_argument("--target-dominance-min", type=float, default=0.8,
                        help="reject a profile trial unless its target shell is this fraction of the largest packet")
    parser.add_argument("--output-modes", type=int, default=16,
                        help="dominant target-shell outputs used by the stratified interaction receipt")
    parser.add_argument("--output-activity-coverage", type=float, default=0.0,
                        help="if positive, enlarge the fixed dominant-output carrier until this modal-activity fraction is covered")
    parser.add_argument("--samples-per-stratum", type=int, default=48)
    parser.add_argument("--exact-check", action="store_true",
                        help="also enumerate the selected finite carrier, for small-N estimator validation")
    parser.add_argument("--evolve", action="store_true",
                        help="evolve the selected profile for one declared parabolic window")
    parser.add_argument("--backend", choices=("cpu", "gpu"), default="cpu")
    parser.add_argument("--dt", type=float, default=1.0e-3)
    parser.add_argument("--window-c", type=float, default=1.0,
                        help="multiple of 2**(-2*target_shell)/nu when --evolve")
    parser.add_argument("--checkpoint-fractions", default="0,0.25,0.5,0.75,1",
                        help="comma-separated fractions of the evolved window to retain in the receipt")
    parser.add_argument("--mechanism-trace-count", type=int, default=0,
                        help=("add this many evenly spaced finite-Galerkin checkpoints for frozen-packet "
                              "coercivity telemetry; interaction sampling remains endpoints only"))
    parser.add_argument("--mechanism-trace-start-fraction", type=float, default=0.0,
                        help="start fraction of the evolved window for evenly spaced mechanism telemetry")
    parser.add_argument("--mechanism-trace-end-fraction", type=float, default=1.0,
                        help="end fraction of the evolved window for evenly spaced mechanism telemetry")
    parser.add_argument("--triad-coherence-samples-per-output", type=int, default=0,
                        help=("when positive, estimate oriented convolution-atom coherence at every mechanism "
                              "checkpoint using this many uniform input samples per frozen-packet output"))
    parser.add_argument("--triad-coherence-batch-size", type=int, default=512,
                        help="output-mode batch size for the optional triad-coherence estimator")
    parser.add_argument("--canonical-triad-samples-per-output", type=int, default=0,
                        help=("when positive, reaggregate sampled ordered convolution atoms into permutation- and "
                              "reality-invariant finite Fourier triad orbits before measuring packet-transfer cancellation"))
    parser.add_argument("--moving-packet-radius", type=int, default=1)
    parser.add_argument("--cfd-root", type=Path, default=DEFAULT_CFD_ROOT)
    parser.add_argument("--fft-backend", default="vkfft-vulkan")
    parser.add_argument("--selection-objective", choices=("chi-match", "short-survival"), default="chi-match",
                        help="short-survival evolves admissible phase trials over --window-c and chooses maximum moving survival")
    parser.add_argument("--require-positive-short-input", action="store_true",
                        help="with short-survival, reject trials whose frozen-initial-packet nonlinear integral is nonpositive")
    parser.add_argument("--save-selected-state", type=Path, default=None,
                        help="write the exact selected raw Fourier state and selection metadata as a compressed NPZ receipt")
    parser.add_argument("--state-input", type=Path, default=None,
                        help="load an exact compressed raw Fourier state saved by --save-selected-state; bypass profile regeneration")
    parser.add_argument("--state-perturbation", choices=("none", "phase", "coherence", "angular", "radial", "helicity"),
                        default="none",
                        help="deterministic transverse perturbation of --state-input before critical renormalisation")
    parser.add_argument("--perturb-epsilon", type=float, default=0.0,
                        help="signed local perturbation magnitude; zero preserves the saved state exactly")
    parser.add_argument("--perturb-seed", type=int, default=20260719,
                        help="deterministic tangent-realisation seed for --state-perturbation")
    parser.add_argument("--continuation-state", action="store_true",
                        help="treat --state-input as a finite-Galerkin restart: preserve its exact state but skip fresh-profile signed-chi and target-dominance gates")
    parser.add_argument("--save-final-state", type=Path, default=None,
                        help="write the exact final raw Fourier state after --evolve as a compressed NPZ checkpoint")
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


def write_json_atomically(path: Path, payload: dict[str, Any]) -> None:
    """Promote a complete JSON receipt with one same-filesystem rename.

    This protects direct invocations as well as manifest-runner invocations:
    a crashed solver may leave no receipt, but it cannot leave a half-written
    JSON file at the declared authority path.  The outer runner is still
    responsible for stdout, stderr, exit-status, and checksum sidecars.
    """
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(
        mode="w", encoding="utf-8", dir=path.parent,
        prefix=f".{path.name}.", suffix=".partial", delete=False,
    ) as handle:
        temporary = Path(handle.name)
        json.dump(payload, handle, indent=2, sort_keys=True)
        handle.write("\n")
        handle.flush()
        os.fsync(handle.fileno())
    try:
        os.replace(temporary, path)
    finally:
        if temporary.exists():
            temporary.unlink()


def mode_index(mode: tuple[int, int, int], n: int) -> tuple[int, int, int]:
    return mode[2] % n, mode[1] % n, mode[0] % n


def negate(mode: tuple[int, int, int]) -> tuple[int, int, int]:
    return tuple(-entry for entry in mode)


def signed_modes(n: int) -> list[tuple[int, int, int]]:
    axis = np.fft.fftfreq(n).astype(np.float64) * n
    modes: list[tuple[int, int, int]] = []
    for zyx in np.ndindex((n, n, n)):
        z, y, x = zyx
        modes.append((int(axis[x]), int(axis[y]), int(axis[z])))
    return modes


def dyadic_weight(norm: np.ndarray) -> np.ndarray:
    return np.where(norm > 0.0, 2.0 ** np.floor(np.log2(np.maximum(norm, 1.0))), 0.0)


def normalise_critical_mass(raw_hat: np.ndarray, critical_mass: float) -> np.ndarray:
    _, norm = frequency_grid(raw_hat.shape[0])
    field_hat = np.moveaxis(raw_hat / float(raw_hat.shape[0] ** 3), -1, 0)
    mass = float(np.sum(dyadic_weight(norm) * np.sum(np.abs(field_hat) ** 2, axis=0)))
    if mass <= 1.0e-30:
        raise ValueError("profile has zero finite critical mass")
    return raw_hat * math.sqrt(critical_mass / mass)


def profile_raw_hat(args: argparse.Namespace, seed: int) -> np.ndarray:
    """Generate one transverse shape representative before critical normalisation."""
    rng = np.random.default_rng(seed)
    n = args.n
    raw = np.zeros((n, n, n, 3), dtype=np.complex128)
    axis = np.asarray(args.angular_axis, dtype=np.float64)
    axis_norm = float(np.linalg.norm(axis))
    if axis_norm <= 1.0e-30:
        raise ValueError("angular axis must be nonzero")
    axis /= axis_norm
    plus_energy = 0.5 * (1.0 + args.helicity_bias)
    minus_energy = 1.0 - plus_energy
    centre = float(2 ** args.target_shell)
    for mode in signed_modes(n):
        if mode == (0, 0, 0) or mode <= negate(mode):
            continue
        vector = np.asarray(mode, dtype=np.float64)
        radius = float(np.linalg.norm(vector))
        if radius <= 0.0 or np.any(np.abs(vector) > n / 3.0):
            continue
        angle = math.acos(float(np.clip(np.dot(vector / radius, axis), -1.0, 1.0)))
        radial = math.log(radius / centre)
        envelope = math.exp(-0.5 * (angle / args.angular_width) ** 2
                            -0.5 * (radial / args.radial_log_width) ** 2)
        if envelope <= 1.0e-14:
            continue
        # Coherence controls only the non-symmetry phase content.  Translation
        # is fixed at the origin, so it is not used as an accidental profile
        # coordinate here.
        common_phase = (1.0 - args.spatial_coherence) * rng.uniform(-math.pi, math.pi)
        relative_phase = rng.uniform(-math.pi, math.pi)
        h_plus, h_minus = helical_basis(mode)
        coefficient = envelope * np.exp(1j * common_phase) * (
            math.sqrt(plus_energy) * h_plus
            + math.sqrt(minus_energy) * np.exp(1j * relative_phase) * h_minus
        )
        raw[mode_index(mode, n)] = coefficient
        raw[mode_index(negate(mode), n)] = np.conjugate(coefficient)
    return normalise_critical_mass(raw, args.critical_mass)


def perturb_saved_state(args: argparse.Namespace, raw_hat: np.ndarray) -> np.ndarray:
    """Apply one state-anchored, reality-preserving local profile deformation.

    The directions are finite-dimensional diagnostics, not tangent vectors to a
    continuum quotient.  They deliberately begin from the exact saved state,
    then restore the declared finite critical mass.  Translation, amplitude,
    and literal dyadic scale copies are not used as perturbation directions.
    """
    if args.state_perturbation == "none" or args.perturb_epsilon == 0.0:
        return raw_hat.copy()
    n = raw_hat.shape[0]
    rng = np.random.default_rng(args.perturb_seed)
    result = raw_hat.copy()
    axis = np.asarray(args.angular_axis, dtype=np.float64)
    axis_norm = float(np.linalg.norm(axis))
    if axis_norm <= 1.0e-30:
        raise ValueError("angular axis must be nonzero")
    axis /= axis_norm
    centre = float(2 ** args.target_shell)
    # Centre real amplitude directions in the finite critical-mass metric so
    # the final normalisation is a small correction rather than the direction.
    weights: list[float] = []
    direction_values: list[float] = []
    representatives: list[tuple[tuple[int, int, int], np.ndarray]] = []
    for mode in signed_modes(n):
        if mode == (0, 0, 0) or mode <= negate(mode):
            continue
        vector = np.asarray(mode, dtype=np.float64)
        radius = float(np.linalg.norm(vector))
        if radius <= 0.0:
            continue
        coefficient = result[mode_index(mode, n)]
        strength = float(np.sum(np.abs(coefficient) ** 2))
        if strength <= 1.0e-30:
            continue
        representatives.append((mode, coefficient.copy()))
        weights.append((2.0 ** math.floor(math.log2(max(radius, 1.0)))) * strength)
        if args.state_perturbation == "angular":
            direction_values.append(float(np.dot(vector / radius, axis)))
        elif args.state_perturbation == "radial":
            direction_values.append(math.log(radius / centre))
        else:
            direction_values.append(0.0)
    weight_array = np.asarray(weights, dtype=np.float64)
    value_array = np.asarray(direction_values, dtype=np.float64)
    if weight_array.size == 0:
        raise ValueError("saved state has no nonzero positive-mode representatives")
    if args.state_perturbation in ("angular", "radial"):
        value_array -= float(np.dot(weight_array, value_array) / np.sum(weight_array))
    for ordinal, ((mode, coefficient), direction) in enumerate(zip(representatives, value_array)):
        index = mode_index(mode, n)
        minus_index = mode_index(negate(mode), n)
        if args.state_perturbation == "phase":
            # Random modal phase is explicitly not an affine translation gauge.
            phase = float(rng.normal())
            updated = coefficient * np.exp(1j * args.perturb_epsilon * phase)
        elif args.state_perturbation == "coherence":
            # Move each modal phase a signed fraction towards a common
            # origin-centred convention.  This is distinct from random phase
            # noise and keeps the state anchored to the exact survivor.
            reference_phase = float(np.angle(np.sum(coefficient)))
            updated = coefficient * np.exp(-1j * args.perturb_epsilon * reference_phase)
        elif args.state_perturbation in ("angular", "radial"):
            updated = coefficient * math.exp(args.perturb_epsilon * float(direction))
        else:  # helicity
            h_plus, h_minus = helical_basis(mode)
            a_plus = np.vdot(h_plus, coefficient)
            a_minus = np.vdot(h_minus, coefficient)
            angle = args.perturb_epsilon * float(rng.choice((-1.0, 1.0)))
            cosine, sine = math.cos(angle), math.sin(angle)
            updated = (cosine * a_plus - sine * a_minus) * h_plus + (sine * a_plus + cosine * a_minus) * h_minus
        result[index] = updated
        result[minus_index] = np.conjugate(updated)
    return normalise_critical_mass(result, args.critical_mass)


def raw_to_field_hat(raw_hat: np.ndarray, wave: np.ndarray, norm_sq: np.ndarray) -> np.ndarray:
    n = raw_hat.shape[0]
    return leray_project(np.moveaxis(raw_hat / float(n ** 3), -1, 0), wave, norm_sq)


def profile_shape_metrics(field_hat: np.ndarray, wave: np.ndarray, norm: np.ndarray) -> dict[str, float]:
    density = np.sum(np.abs(field_hat) ** 2, axis=0)
    total = float(np.sum(density))
    nonzero = norm > 0.0
    weights = density[nonzero]
    radii = norm[nonzero]
    directions = wave[:, nonzero] / radii[None, :]
    probability = weights / float(np.sum(weights))
    second_moment = (directions * probability[None, :]) @ directions.T
    angular_concentration = float(np.linalg.eigvalsh(second_moment)[-1])
    log_radius = np.log(radii)
    mean_log_radius = float(np.sum(probability * log_radius))
    radial_width = float(np.sqrt(np.sum(probability * (log_radius - mean_log_radius) ** 2)))
    velocity = np.fft.ifftn(np.moveaxis(field_hat * float(field_hat.shape[1] ** 3), 0, -1), axes=(0, 1, 2)).real
    physical_density = np.sum(velocity ** 2, axis=-1)
    physical_probability = physical_density.ravel() / max(float(np.sum(physical_density)), 1.0e-30)
    spatial_ipr_fraction = float(1.0 / (physical_probability.size * np.sum(physical_probability ** 2)))
    positive = physical_probability[physical_probability > 0.0]
    spatial_entropy_fraction = float(math.exp(-np.sum(positive * np.log(positive))) / physical_probability.size)
    return {
        "finite_critical_mass": float(np.sum(dyadic_weight(norm) * density)),
        "angular_second_moment_operator_fraction": angular_concentration,
        "radial_log_width": radial_width,
        "spatial_inverse_participation_fraction": spatial_ipr_fraction,
        "spatial_shannon_effective_fraction": spatial_entropy_fraction,
    }


def static_metrics(args: argparse.Namespace, field_hat: np.ndarray, wave: np.ndarray,
                   norm: np.ndarray, norm_sq: np.ndarray) -> tuple[np.ndarray, dict[str, float]]:
    dealias = component_dealias_mask(wave, args.n)
    nonlinear_hat = reconstructed_nonlinear_rhs(field_hat, wave, norm_sq, dealias)
    max_shell = int(math.ceil(math.log2(float(np.max(norm)) + 1.0)))
    packets = dyadic_shell_packets(field_hat, norm, max_shell)
    dissipations = shell_dissipation(field_hat, norm_sq, norm, max_shell)
    nonlinear_rates = shell_nonlinear_rate(field_hat, nonlinear_hat, norm, max_shell)
    target_dissipation = float(dissipations[args.target_shell])
    target_nonlinear = float(nonlinear_rates[args.target_shell])
    viscous_rate = 2.0 * args.nu * target_dissipation
    return nonlinear_hat, {
        "target_packet": float(packets[args.target_shell]),
        "target_packet_dominance": float(packets[args.target_shell] / max(float(np.max(packets)), 1.0e-30)),
        "target_nonlinear_rate": target_nonlinear,
        "target_viscous_rate": viscous_rate,
        "chi_signed": target_nonlinear / viscous_rate if viscous_rate > 1.0e-30 else math.nan,
        "chi_absolute": abs(target_nonlinear) / viscous_rate if viscous_rate > 1.0e-30 else math.nan,
    }


def frozen_packet_coercivity_factors(
    field_hat: np.ndarray, nonlinear_hat: np.ndarray, norm: np.ndarray, norm_sq: np.ndarray,
    frozen_lower: int, frozen_upper: int, nu: float,
) -> dict[str, float]:
    """Factor the frozen packet's positive coercivity ratio exactly.

    The packet energy convention weights shell ``j`` by ``2**j``.  Writing
    ``p = <u, N>_w``, ``P = ||u||_w**2`` and ``D = ||grad u||_w**2`` gives

        [2 Re p]_+ / (2 nu D)
        = (||N||_w / (nu sqrt(D))) (sqrt(P) / sqrt(D)) alignment_+.

    This is finite telemetry only.  It deliberately avoids attributing a
    subsequent Gamma drop to broadening, angular dispersion, or phase
    cancellation before the three factors have been compared across traces.
    """
    weighted_packet = 0.0
    weighted_gradient = 0.0
    weighted_forcing = 0.0
    pairing = 0.0j
    for shell in range(frozen_lower, frozen_upper):
        lower = float(2 ** shell)
        upper = float(2 ** (shell + 1))
        mask = (norm >= lower) & (norm < upper)
        weight = float(2 ** shell)
        packet_modes = field_hat[:, mask]
        forcing_modes = nonlinear_hat[:, mask]
        weighted_packet += weight * float(np.sum(np.abs(packet_modes) ** 2))
        weighted_gradient += weight * float(np.sum(norm_sq[mask] * np.abs(packet_modes) ** 2))
        weighted_forcing += weight * float(np.sum(np.abs(forcing_modes) ** 2))
        pairing += weight * np.sum(np.conjugate(packet_modes) * forcing_modes)
    packet_norm = math.sqrt(max(weighted_packet, 0.0))
    gradient_norm = math.sqrt(max(weighted_gradient, 0.0))
    forcing_norm = math.sqrt(max(weighted_forcing, 0.0))
    denominator = packet_norm * forcing_norm
    signed_alignment = float(np.real(pairing) / denominator) if denominator > 1.0e-30 else 0.0
    positive_alignment = max(signed_alignment, 0.0)
    viscous_rate = 2.0 * nu * weighted_gradient
    positive_gamma = max(2.0 * float(np.real(pairing)), 0.0) / viscous_rate if viscous_rate > 1.0e-30 else math.nan
    forcing_to_viscous_gradient = (
        forcing_norm / (nu * gradient_norm) if gradient_norm > 1.0e-30 else math.nan
    )
    packet_to_gradient = packet_norm / gradient_norm if gradient_norm > 1.0e-30 else math.nan
    reconstructed_gamma = forcing_to_viscous_gradient * packet_to_gradient * positive_alignment
    return {
        "weighted_packet_norm": packet_norm,
        "weighted_gradient_norm": gradient_norm,
        "weighted_nonlinear_forcing_norm": forcing_norm,
        "weighted_pairing_real": float(np.real(pairing)),
        "weighted_pairing_imaginary": float(np.imag(pairing)),
        "signed_nonlinear_alignment": signed_alignment,
        "positive_nonlinear_alignment": positive_alignment,
        "forcing_to_viscous_gradient_ratio": forcing_to_viscous_gradient,
        "packet_to_gradient_ratio": packet_to_gradient,
        "positive_coercivity_ratio_from_factors": reconstructed_gamma,
        "positive_coercivity_ratio_direct": positive_gamma,
        "positive_coercivity_factorisation_residual": reconstructed_gamma - positive_gamma,
    }


def oriented_atom_vectors(
    field_flat: np.ndarray, wave_flat: np.ndarray, output_flat: np.ndarray, input_flat: np.ndarray,
) -> np.ndarray:
    """Return oriented Fourier convolution atoms for ``N(output)``.

    The atoms are indexed by an output coefficient ``k`` and one ordered input
    coefficient ``p``; the other input is ``q = k - p`` on the FFT torus.  This
    is deliberately an *oriented atom* decomposition rather than a canonical
    unordered triad decomposition.  It has the exact finite identity

        sum_p atom(k, p) = N_hat(k),

    which makes uniform input sampling straightforward.  The associated
    unsigned atom sums are empirical estimators, not formal triad bounds.
    """
    n = int(round(field_flat.shape[1] ** (1.0 / 3.0)))
    output_coords = np.column_stack(np.unravel_index(output_flat, (n, n, n)))
    input_coords = np.column_stack(np.unravel_index(input_flat.ravel(), (n, n, n))).reshape(
        input_flat.shape + (3,)
    )
    other_coords = (output_coords[:, None, :] - input_coords) % n
    other_flat = np.ravel_multi_index(other_coords.reshape(-1, 3).T, (n, n, n)).reshape(input_flat.shape)
    up = field_flat[:, input_flat]
    uq = field_flat[:, other_flat]
    kq = wave_flat[:, other_flat]
    atoms = -1j * np.sum(kq * up, axis=0)[None, :] * uq
    output_wave = wave_flat[:, output_flat]
    output_norm_sq = np.sum(output_wave * output_wave, axis=0)
    nonzero = output_norm_sq > 0.0
    if np.any(nonzero):
        dot = np.sum(output_wave[:, :, None] * atoms, axis=0)
        atoms[:, nonzero, :] -= (
            output_wave[:, nonzero, None] * dot[None, nonzero, :] / output_norm_sq[nonzero][None, :, None]
        )
    return atoms


def oriented_atom_pair_vectors(
    field_flat: np.ndarray, wave_flat: np.ndarray, output_flat: np.ndarray, input_flat: np.ndarray,
) -> np.ndarray:
    """Return convolution atoms for equally-sized arrays of ordered pairs.

    This is the pairwise counterpart of :func:`oriented_atom_vectors`.  It is
    used only to reaggregate the complete permutation/reality orbit belonging
    to a sampled pair; it deliberately does not define a new Navier--Stokes
    transfer convention.
    """
    n = int(round(field_flat.shape[1] ** (1.0 / 3.0)))
    output_coords = np.column_stack(np.unravel_index(output_flat, (n, n, n)))
    input_coords = np.column_stack(np.unravel_index(input_flat, (n, n, n)))
    other_coords = (output_coords - input_coords) % n
    other_flat = np.ravel_multi_index(other_coords.T, (n, n, n))
    up, uq = field_flat[:, input_flat], field_flat[:, other_flat]
    kq = wave_flat[:, other_flat]
    atoms = -1j * np.sum(kq * up, axis=0)[None, :] * uq
    output_wave = wave_flat[:, output_flat]
    output_norm_sq = np.sum(output_wave * output_wave, axis=0)
    nonzero = output_norm_sq > 0.0
    if np.any(nonzero):
        dot = np.sum(output_wave * atoms, axis=0)
        atoms[:, nonzero] -= output_wave[:, nonzero] * dot[nonzero] / output_norm_sq[nonzero]
    return atoms


def mode_to_flat(mode: tuple[int, int, int], n: int) -> int:
    """Map an integer Fourier mode in (x, y, z) order to FFT-flat storage."""
    x, y, z = mode
    return int(np.ravel_multi_index((z % n, y % n, x % n), (n, n, n)))


def canonical_reality_orbit_pairs(
    output_flat: int, input_flat: int, wave_flat: np.ndarray, n: int, frozen_outputs: set[int],
) -> tuple[tuple[tuple[int, int, int], ...], tuple[tuple[int, int], ...]]:
    """Return the canonical reality-orbit key and all frozen-packet atom pairs.

    Starting from ``N_hat(output)[input]``, the geometric triad is
    ``{-output, input, output-input}``.  We include every output-leg and input
    ordering, then its reality partner, and retain only output modes in the
    fixed packet.  Summing the associated scalar pairings is consequently an
    exact packet-transfer contribution for one permutation- and
    reality-invariant orbit.  This is a finite reaggregation convention, not
    a claim that an individual oriented atom is a physical triad transfer.
    """
    out = tuple(int(value) for value in wave_flat[:, output_flat])
    left = tuple(int(value) for value in wave_flat[:, input_flat])
    output_coords = np.unravel_index(output_flat, (n, n, n))
    input_coords = np.unravel_index(input_flat, (n, n, n))
    other_coords = tuple((output_coords[index] - input_coords[index]) % n for index in range(3))
    other_flat = int(np.ravel_multi_index(other_coords, (n, n, n)))
    right = tuple(int(value) for value in wave_flat[:, other_flat])
    triad = (tuple(-value for value in out), left, right)
    negative = tuple(tuple(-value for value in mode) for mode in triad)
    key = min(tuple(sorted(triad)), tuple(sorted(negative)))
    pairs: set[tuple[int, int]] = set()
    for representative in (triad, negative):
        for leg_index, leg in enumerate(representative):
            remaining = [representative[index] for index in range(3) if index != leg_index]
            output = mode_to_flat(tuple(-value for value in leg), n)
            if output not in frozen_outputs:
                continue
            for input_mode in remaining:
                pairs.add((output, mode_to_flat(input_mode, n)))
    if not pairs:
        raise RuntimeError("sampled frozen-packet atom lost all canonical orbit representatives")
    return key, tuple(sorted(pairs))


def canonical_triad_coherence_estimate(
    field_hat: np.ndarray, nonlinear_hat: np.ndarray, norm: np.ndarray,
    frozen_lower: int, frozen_upper: int, samples_per_output: int,
    batch_size: int, rng: np.random.Generator,
) -> dict[str, Any]:
    """Estimate cancellation after canonical permutation/reality reaggregation.

    The numerator is the exact frozen-packet pairing.  For each uniformly
    sampled ordered atom, this routine evaluates its entire canonical orbit,
    including all input swaps and the reality partner, *before* taking an
    absolute value.  Dividing by the number of retained atom representatives
    makes the unsigned orbit envelope an unbiased finite-population estimate.

    The result answers whether cancellation visible in the ordered atom basis
    survives this physical-orbit reaggregation.  Its denominators remain
    sampled finite-Galerkin telemetry, not certified bounds.
    """
    if samples_per_output <= 0:
        return {"status": "disabled"}
    n = field_hat.shape[1]
    flat_count = n ** 3
    flat_norm = norm.ravel()
    mask = (flat_norm >= float(2 ** frozen_lower)) & (flat_norm < float(2 ** frozen_upper))
    outputs = np.flatnonzero(mask)
    if outputs.size == 0:
        return {"status": "empty_frozen_packet"}
    frozen_outputs = {int(value) for value in outputs}
    field_flat = field_hat.reshape(3, -1)
    nonlinear_flat = nonlinear_hat.reshape(3, -1)
    wave, _ = frequency_grid(n)
    wave_flat = wave.reshape(3, -1)
    weights = np.power(2.0, np.floor(np.log2(np.maximum(flat_norm[outputs], 1.0))))
    exact_pairing = np.sum(weights[None, :] * np.conjugate(field_flat[:, outputs]) * nonlinear_flat[:, outputs])
    orbit_abs_sum = 0.0
    orbit_abs_sq_error = 0.0
    atom_abs_sum = 0.0
    atom_abs_sq_error = 0.0
    regrouped_pairing_sum = 0.0
    regrouped_pairing_sq_error = 0.0
    for start in range(0, outputs.size, batch_size):
        batch = outputs[start:start + batch_size]
        draw = rng.integers(0, flat_count, size=(batch.size, samples_per_output), dtype=np.int64)
        sample_outputs = np.repeat(batch, samples_per_output)
        sample_inputs = draw.ravel()
        group_pairs: list[tuple[tuple[int, int], ...]] = []
        group_offsets = [0]
        for output, input_mode in zip(sample_outputs, sample_inputs, strict=True):
            _, pairs = canonical_reality_orbit_pairs(
                int(output), int(input_mode), wave_flat, n, frozen_outputs,
            )
            group_pairs.append(pairs)
            group_offsets.append(group_offsets[-1] + len(pairs))
        all_outputs = np.fromiter((pair[0] for pairs in group_pairs for pair in pairs), dtype=np.int64)
        all_inputs = np.fromiter((pair[1] for pairs in group_pairs for pair in pairs), dtype=np.int64)
        all_atoms = oriented_atom_pair_vectors(field_flat, wave_flat, all_outputs, all_inputs)
        all_weights = np.power(2.0, np.floor(np.log2(np.maximum(flat_norm[all_outputs], 1.0))))
        all_scalars = np.real(all_weights * np.sum(np.conjugate(field_flat[:, all_outputs]) * all_atoms, axis=0))
        orbit_values = np.empty(sample_outputs.size, dtype=np.float64)
        orbit_abs_values = np.empty(sample_outputs.size, dtype=np.float64)
        atom_abs_values = np.empty(sample_outputs.size, dtype=np.float64)
        for index, (left, right) in enumerate(zip(group_offsets[:-1], group_offsets[1:], strict=True)):
            orbit_value = float(np.sum(all_scalars[left:right]))
            multiplicity = float(right - left)
            orbit_values[index] = orbit_value / multiplicity
            orbit_abs_values[index] = abs(orbit_value) / multiplicity
            atom_abs_values[index] = float(np.sum(np.abs(all_scalars[left:right]))) / multiplicity
        orbit_values = orbit_values.reshape(batch.size, samples_per_output)
        orbit_abs_values = orbit_abs_values.reshape(batch.size, samples_per_output)
        atom_abs_values = atom_abs_values.reshape(batch.size, samples_per_output)
        population = float(flat_count)
        regrouped_pairing_sum += float(population * np.sum(np.mean(orbit_values, axis=1)))
        orbit_abs_sum += float(population * np.sum(np.mean(orbit_abs_values, axis=1)))
        atom_abs_sum += float(population * np.sum(np.mean(atom_abs_values, axis=1)))
        if samples_per_output > 1:
            regrouped_pairing_sq_error += float(np.sum(population ** 2 * np.var(orbit_values, axis=1, ddof=1) / samples_per_output))
            orbit_abs_sq_error += float(np.sum(population ** 2 * np.var(orbit_abs_values, axis=1, ddof=1) / samples_per_output))
            atom_abs_sq_error += float(np.sum(population ** 2 * np.var(atom_abs_values, axis=1, ddof=1) / samples_per_output))

    def ratio_interval(numerator: float, denominator: float, variance: float) -> list[float] | None:
        if denominator <= 1.0e-30 or not math.isfinite(variance):
            return None
        error = 1.96 * math.sqrt(max(variance, 0.0))
        return [numerator / (denominator + error), min(1.0, numerator / max(denominator - error, 1.0e-30))]

    canonical_coherence = abs(float(np.real(exact_pairing))) / orbit_abs_sum if orbit_abs_sum > 1.0e-30 else math.nan
    positive_efficiency = max(float(np.real(exact_pairing)), 0.0) / orbit_abs_sum if orbit_abs_sum > 1.0e-30 else math.nan
    internal_cancellation = orbit_abs_sum / atom_abs_sum if atom_abs_sum > 1.0e-30 else math.nan
    return {
        "status": "sampled_canonical_reality_orbits",
        "orbit_convention": (
            "canonical unordered geometric triad modulo its reality partner; scalar packet transfer is the sum of all "
            "ordered convolution atoms for that orbit and frozen-packet output legs before absolute value"
        ),
        "sampled_output_mode_count": int(outputs.size),
        "samples_per_output": int(samples_per_output),
        "canonical_real_transfer_coherence": canonical_coherence,
        "canonical_real_transfer_coherence_nominal_95_percent_interval": ratio_interval(
            abs(float(np.real(exact_pairing))), orbit_abs_sum, orbit_abs_sq_error,
        ),
        "canonical_positive_transfer_efficiency": positive_efficiency,
        "estimated_unsigned_canonical_packet_transfer_envelope": orbit_abs_sum,
        "estimated_unsigned_ordered_atom_packet_transfer_envelope": atom_abs_sum,
        "internal_ordered_atom_cancellation_ratio": internal_cancellation,
        "exact_packet_pairing_real": float(np.real(exact_pairing)),
        "estimated_regrouped_packet_pairing": regrouped_pairing_sum,
        "estimated_regrouped_packet_pairing_nominal_95_percent_interval": [
            regrouped_pairing_sum - 1.96 * math.sqrt(max(regrouped_pairing_sq_error, 0.0)),
            regrouped_pairing_sum + 1.96 * math.sqrt(max(regrouped_pairing_sq_error, 0.0)),
        ],
        "regrouping_exact_numerator_difference": regrouped_pairing_sum - float(np.real(exact_pairing)),
        "warning": (
            "canonical-orbit denominators are sampled finite-Galerkin estimates. The exact packet pairing is independent "
            "of the orbit convention, but no confidence interval here is a certified enclosure or continuum theorem."
        ),
    }


def triad_coherence_estimate(
    field_hat: np.ndarray, nonlinear_hat: np.ndarray, norm: np.ndarray, norm_sq: np.ndarray,
    frozen_lower: int, frozen_upper: int, nu: float, samples_per_output: int,
    batch_size: int, rng: np.random.Generator,
) -> dict[str, Any]:
    """Estimate cancellation among oriented convolution atoms in a frozen packet.

    The total packet forcing and total packet pairing are computed exactly from
    ``nonlinear_hat``.  Only the unsigned denominators are sampled.  Hence the
    ratios below have an exact numerator and a Monte-Carlo denominator with a
    stated normal-approximation interval.  They distinguish cancellation among
    atoms from rotation of their already-summed resultant.
    """
    if samples_per_output <= 0:
        return {"status": "disabled"}
    n = field_hat.shape[1]
    flat_count = n ** 3
    flat_norm = norm.ravel()
    flat_norm_sq = norm_sq.ravel()
    mask = (flat_norm >= float(2 ** frozen_lower)) & (flat_norm < float(2 ** frozen_upper))
    outputs = np.flatnonzero(mask)
    if outputs.size == 0:
        return {"status": "empty_frozen_packet"}
    field_flat = field_hat.reshape(3, -1)
    nonlinear_flat = nonlinear_hat.reshape(3, -1)
    wave, _ = frequency_grid(n)
    wave_flat = wave.reshape(3, -1)
    weights = np.power(2.0, np.floor(np.log2(np.maximum(flat_norm[outputs], 1.0))))
    exact_forcing_sq = float(np.sum(weights[None, :] * np.abs(nonlinear_flat[:, outputs]) ** 2))
    exact_forcing_norm = math.sqrt(max(exact_forcing_sq, 0.0))
    exact_pairing = np.sum(weights[None, :] * np.conjugate(field_flat[:, outputs]) * nonlinear_flat[:, outputs])
    vector_sum = 0.0
    vector_sq_error = 0.0
    scalar_abs_sum = 0.0
    scalar_abs_sq_error = 0.0
    scalar_real_abs_sum = 0.0
    scalar_real_abs_sq_error = 0.0
    for start in range(0, outputs.size, batch_size):
        batch = outputs[start:start + batch_size]
        draw = rng.integers(0, flat_count, size=(batch.size, samples_per_output), dtype=np.int64)
        atoms = oriented_atom_vectors(field_flat, wave_flat, batch, draw)
        batch_weight = np.power(2.0, np.floor(np.log2(np.maximum(flat_norm[batch], 1.0))))
        vector_values = np.sqrt(batch_weight[:, None] * np.sum(np.abs(atoms) ** 2, axis=0))
        z_values = batch_weight[:, None] * np.sum(np.conjugate(field_flat[:, batch])[:, :, None] * atoms, axis=0)
        scalar_values = np.abs(z_values)
        scalar_real_values = np.abs(np.real(z_values))
        population = float(flat_count)
        vector_sum += float(population * np.sum(np.mean(vector_values, axis=1)))
        scalar_abs_sum += float(population * np.sum(np.mean(scalar_values, axis=1)))
        scalar_real_abs_sum += float(population * np.sum(np.mean(scalar_real_values, axis=1)))
        if samples_per_output > 1:
            vector_sq_error += float(np.sum(population ** 2 * np.var(vector_values, axis=1, ddof=1) / samples_per_output))
            scalar_abs_sq_error += float(np.sum(population ** 2 * np.var(scalar_values, axis=1, ddof=1) / samples_per_output))
            scalar_real_abs_sq_error += float(np.sum(population ** 2 * np.var(scalar_real_values, axis=1, ddof=1) / samples_per_output))
    gradient_sq = float(np.sum(weights * flat_norm_sq[outputs] * np.sum(np.abs(field_flat[:, outputs]) ** 2, axis=0)))
    packet_sq = float(np.sum(weights * np.sum(np.abs(field_flat[:, outputs]) ** 2, axis=0)))
    gradient_norm = math.sqrt(max(gradient_sq, 0.0))
    packet_norm = math.sqrt(max(packet_sq, 0.0))
    signed_alignment = (
        float(np.real(exact_pairing)) / (packet_norm * exact_forcing_norm)
        if packet_norm * exact_forcing_norm > 1.0e-30 else 0.0
    )
    def ratio_interval(numerator: float, denominator: float, variance: float) -> list[float] | None:
        if denominator <= 1.0e-30 or not math.isfinite(variance):
            return None
        error = 1.96 * math.sqrt(max(variance, 0.0))
        lower_denominator = max(denominator - error, 1.0e-30)
        upper_denominator = denominator + error
        return [numerator / upper_denominator, min(1.0, numerator / lower_denominator)]
    vector_coherence = exact_forcing_norm / vector_sum if vector_sum > 1.0e-30 else math.nan
    phase_coherence = abs(exact_pairing) / scalar_abs_sum if scalar_abs_sum > 1.0e-30 else math.nan
    sign_coherence = abs(float(np.real(exact_pairing))) / scalar_real_abs_sum if scalar_real_abs_sum > 1.0e-30 else math.nan
    raw_forcing = vector_sum / (nu * gradient_norm) if gradient_norm > 1.0e-30 else math.nan
    packet_geometry = packet_norm / gradient_norm if gradient_norm > 1.0e-30 else math.nan
    reconstructed_gamma = raw_forcing * vector_coherence * packet_geometry * max(signed_alignment, 0.0)
    direct_gamma = (
        max(2.0 * float(np.real(exact_pairing)), 0.0) / (2.0 * nu * gradient_sq)
        if gradient_sq > 1.0e-30 else math.nan
    )
    return {
        "status": "sampled_oriented_convolution_atoms",
        "atom_convention": "ordered p,q=k-p Fourier convolution atoms; not canonical unordered triads",
        "sampled_output_mode_count": int(outputs.size),
        "samples_per_output": int(samples_per_output),
        "raw_triadic_forcing_to_viscous_gradient_ratio": raw_forcing,
        "inter_triad_vector_coherence": vector_coherence,
        "inter_triad_vector_coherence_nominal_95_percent_interval": ratio_interval(exact_forcing_norm, vector_sum, vector_sq_error),
        "packet_direction_alignment_from_exact_resultant": max(signed_alignment, 0.0),
        "packet_direction_alignment_signed": signed_alignment,
        "packet_to_gradient_ratio": packet_geometry,
        "scalar_phase_coherence": phase_coherence,
        "scalar_phase_coherence_nominal_95_percent_interval": ratio_interval(abs(exact_pairing), scalar_abs_sum, scalar_abs_sq_error),
        "scalar_real_sign_coherence": sign_coherence,
        "scalar_real_sign_coherence_nominal_95_percent_interval": ratio_interval(abs(float(np.real(exact_pairing))), scalar_real_abs_sum, scalar_real_abs_sq_error),
        "positive_transfer_efficiency": max(float(np.real(exact_pairing)), 0.0) / scalar_abs_sum if scalar_abs_sum > 1.0e-30 else math.nan,
        "exact_resultant_forcing_norm": exact_forcing_norm,
        "estimated_unsigned_vector_atom_sum": vector_sum,
        "estimated_unsigned_scalar_pairing_sum": scalar_abs_sum,
        "estimated_unsigned_real_pairing_sum": scalar_real_abs_sum,
        "exact_packet_pairing_real": float(np.real(exact_pairing)),
        "exact_packet_pairing_imaginary": float(np.imag(exact_pairing)),
        "positive_coercivity_ratio_direct": direct_gamma,
        "positive_coercivity_ratio_reconstructed": reconstructed_gamma,
        "positive_coercivity_ratio_reconstruction_residual": reconstructed_gamma - direct_gamma,
        "warning": (
            "denominator intervals account only for independent uniform input sampling within each output; "
            "they are not certified enclosures and do not imply a continuum triad-dephasing theorem"
        ),
    }


def load_cfd_module(args: argparse.Namespace) -> Any:
    scripts_dir = args.cfd_root / "scripts"
    if not scripts_dir.is_dir():
        raise FileNotFoundError(f"missing sibling dashiCFD scripts directory: {scripts_dir}")
    sys.path.insert(0, str(scripts_dir))
    spec = importlib.util.spec_from_file_location("dashi_profile_truth3d", scripts_dir / "make_truth_3d.py")
    if spec is None or spec.loader is None:
        raise RuntimeError("could not load sibling finite-Galerkin solver")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def packet_telemetry(args: argparse.Namespace, field_hat: np.ndarray, wave: np.ndarray,
                     norm: np.ndarray, norm_sq: np.ndarray, time: float,
                     initial_field: np.ndarray, frozen_centre: int,
                     previous_centre: int | None = None) -> dict[str, Any]:
    max_shell = int(math.ceil(math.log2(float(np.max(norm)) + 1.0)))
    packets = dyadic_shell_packets(field_hat, norm, max_shell)
    centre = int(np.argmax(packets))
    moving = float(np.sum(packets[max(0, centre - args.moving_packet_radius):min(len(packets), centre + args.moving_packet_radius + 1)]))
    heat = initial_field * np.exp(-args.nu * norm_sq * time)[None, :]
    heat_packets = dyadic_shell_packets(heat, norm, max_shell)
    heat_centre = int(np.argmax(heat_packets))
    heat_moving = float(np.sum(heat_packets[max(0, heat_centre - args.moving_packet_radius):min(len(heat_packets), heat_centre + args.moving_packet_radius + 1)]))
    nonlinear, static = static_metrics(args, field_hat, wave, norm, norm_sq)
    dissipations = shell_dissipation(field_hat, norm_sq, norm, max_shell)
    nonlinear_shell_rates = shell_nonlinear_rate(field_hat, nonlinear, norm, max_shell)
    moving_lower = max(0, centre - args.moving_packet_radius)
    moving_upper = min(len(packets), centre + args.moving_packet_radius + 1)
    frozen_lower = max(0, frozen_centre - args.moving_packet_radius)
    frozen_upper = min(len(packets), frozen_centre + args.moving_packet_radius + 1)
    previous_lower = max(0, (previous_centre if previous_centre is not None else centre) - args.moving_packet_radius)
    previous_upper = min(len(packets), (previous_centre if previous_centre is not None else centre) + args.moving_packet_radius + 1)
    frozen_nonlinear = float(np.sum(nonlinear_shell_rates[frozen_lower:frozen_upper]))
    frozen_viscous = float(2.0 * args.nu * np.sum(dissipations[frozen_lower:frozen_upper]))
    frozen_factors = frozen_packet_coercivity_factors(
        field_hat, nonlinear, norm, norm_sq, frozen_lower, frozen_upper, args.nu,
    )
    triad_coherence = triad_coherence_estimate(
        field_hat, nonlinear, norm, norm_sq, frozen_lower, frozen_upper, args.nu,
        args.triad_coherence_samples_per_output, args.triad_coherence_batch_size,
        np.random.default_rng(args.seed + 1900003 + int(round(time / args.dt))),
    )
    canonical_triad_coherence = canonical_triad_coherence_estimate(
        field_hat, nonlinear, norm, frozen_lower, frozen_upper,
        args.canonical_triad_samples_per_output, args.triad_coherence_batch_size,
        np.random.default_rng(args.seed + 2900003 + int(round(time / args.dt))),
    )
    return {
        "time": time,
        "shell_packets": [float(value) for value in packets],
        "dominant_shell": centre,
        "moving_packet": moving,
        "frozen_initial_packet": float(np.sum(packets[frozen_lower:frozen_upper])),
        "moving_packet_nonlinear_rate": float(np.sum(nonlinear_shell_rates[moving_lower:moving_upper])),
        "moving_packet_viscous_rate": float(2.0 * args.nu * np.sum(dissipations[moving_lower:moving_upper])),
        "frozen_initial_packet_nonlinear_rate": frozen_nonlinear,
        "frozen_initial_packet_positive_coercivity_ratio": (
            max(frozen_nonlinear, 0.0) / frozen_viscous if frozen_viscous > 1.0e-30 else math.nan
        ),
        "frozen_initial_packet_signed_coercivity_ratio": (
            frozen_nonlinear / frozen_viscous if frozen_viscous > 1.0e-30 else math.nan
        ),
        "frozen_initial_packet_viscous_rate": frozen_viscous,
        "frozen_initial_packet_coercivity_factors": frozen_factors,
        "frozen_initial_packet_triad_coherence": triad_coherence,
        "frozen_initial_packet_canonical_triad_coherence": canonical_triad_coherence,
        "moving_packet_if_previous_centre": float(np.sum(packets[previous_lower:previous_upper])),
        "checkpoint_recentering_jump": float(np.sum(packets[moving_lower:moving_upper]) - np.sum(packets[previous_lower:previous_upper])),
        "heat_moving_packet_exact_spectrum": heat_moving,
        "heat_frozen_initial_packet_exact_spectrum": float(np.sum(heat_packets[frozen_lower:frozen_upper])),
        "profile_shape_metrics": profile_shape_metrics(field_hat, wave, norm),
        "static_packet_metrics": static,
        "_nonlinear": nonlinear,
    }


def coarse_distribution(estimate: dict[str, Any]) -> dict[tuple[int, ...], float]:
    weights: dict[tuple[int, ...], float] = {}
    total = max(float(estimate["absolute_activity_estimate"]), 1.0e-30)
    for row in estimate["strata"]:
        key = tuple(int(row[name]) for name in (
            "shell_offset_left", "shell_offset_right", "angle_bin", "locality_log2_bin",
            "helicity_output", "helicity_left", "helicity_right",
        ))
        weights[key] = max(0.0, float(row["absolute_activity_estimate"])) / total
    return weights


def hellinger_squared(left: dict[tuple[int, ...], float], right: dict[tuple[int, ...], float]) -> float:
    return float(0.5 * sum((math.sqrt(left.get(key, 0.0)) - math.sqrt(right.get(key, 0.0))) ** 2
                           for key in left.keys() | right.keys()))


def evolve_profile(args: argparse.Namespace, raw: np.ndarray, wave: np.ndarray,
                   norm: np.ndarray, norm_sq: np.ndarray) -> dict[str, Any]:
    """Finite-Galerkin trajectory receipt for one already-normalized profile."""
    module = load_cfd_module(args)
    nominal_time = args.window_c * (2.0 ** (-2 * args.target_shell)) / args.nu
    steps = int(math.ceil(nominal_time / args.dt))
    actual_time = steps * args.dt
    initial = raw_to_field_hat(raw, wave, norm_sq)
    initial_packets = dyadic_shell_packets(initial, norm, int(math.ceil(math.log2(float(np.max(norm)) + 1.0))))
    frozen_centre = int(np.argmax(initial_packets))
    checkpoint_fractions = sorted({float(item) for item in args.checkpoint_fractions.split(",")})
    if not checkpoint_fractions or checkpoint_fractions[0] < 0.0 or checkpoint_fractions[-1] > 1.0:
        raise ValueError("checkpoint fractions must lie in [0, 1]")
    checkpoints = {int(round(fraction * steps)) for fraction in checkpoint_fractions}
    if args.mechanism_trace_count:
        checkpoints.update({
            int(round((args.mechanism_trace_start_fraction
                       + (args.mechanism_trace_end_fraction - args.mechanism_trace_start_fraction)
                       * index / args.mechanism_trace_count) * steps))
            for index in range(args.mechanism_trace_count + 1)
        })
    checkpoints.update({0, steps})
    history: list[dict[str, Any]] = []
    coarse_at: dict[int, dict[str, Any]] = {}
    final_raw: np.ndarray | None = None

    def record(step: int, current_raw: np.ndarray) -> None:
        field = raw_to_field_hat(current_raw, wave, norm_sq)
        previous_centre = int(history[-1]["dominant_shell"]) if history else None
        row = packet_telemetry(args, field, wave, norm, norm_sq, step * args.dt, initial,
                               frozen_centre, previous_centre)
        nonlinear = row.pop("_nonlinear")
        if step in {0, steps}:
            coarse_at[step] = stratified_interaction_estimate(
                args, field, nonlinear, wave, norm, np.random.default_rng(args.seed + 7001 + step)
            )
        history.append({"step": step, **row})

    if args.backend == "gpu":
        from vulkan_truth3d_backend import VulkanTruth3DBackend
        backend = VulkanTruth3DBackend(args.n, dt=args.dt, nu0=args.nu, length=2.0 * math.pi,
                                       fft_backend=args.fft_backend)
        try:
            backend.set_initial_u_hat(raw)
            for step in range(steps + 1):
                if step in checkpoints:
                    observed = np.asarray(backend.read_u_hat(), dtype=np.complex128)
                    record(step, observed)
                    if step == steps:
                        final_raw = observed.copy()
                if step < steps:
                    backend.step()
        finally:
            backend.close()
    else:
        _, kx, ky, kz, k2, _ = module.make_grid(args.n, 2.0 * math.pi)
        mask = module.component_dealias_mask(kx, ky, kz, args.n, 2.0 * math.pi)
        current = raw.copy()
        for step in range(steps + 1):
            if step in checkpoints:
                record(step, current)
                if step == steps:
                    final_raw = current.copy()
            if step < steps:
                current = module.rk2_step(current, kx, ky, kz, k2, mask, args.dt, args.nu)
    initial_row, endpoint = history[0], history[-1]
    if final_raw is None:
        raise RuntimeError("finite-Galerkin evolution did not retain its final state")
    initial_coarse, endpoint_coarse = coarse_at[0], coarse_at[steps]
    times = np.asarray([row["time"] for row in history], dtype=np.float64)
    target_nonlinear = np.asarray([row["static_packet_metrics"]["target_nonlinear_rate"] for row in history], dtype=np.float64)
    target_viscous = np.asarray([row["static_packet_metrics"]["target_viscous_rate"] for row in history], dtype=np.float64)
    moving_nonlinear = np.asarray([row["moving_packet_nonlinear_rate"] for row in history], dtype=np.float64)
    moving_viscous = np.asarray([row["moving_packet_viscous_rate"] for row in history], dtype=np.float64)
    frozen_nonlinear = np.asarray([row["frozen_initial_packet_nonlinear_rate"] for row in history], dtype=np.float64)
    frozen_viscous = np.asarray([row["frozen_initial_packet_viscous_rate"] for row in history], dtype=np.float64)
    recentering_jumps = np.asarray([row["checkpoint_recentering_jump"] for row in history], dtype=np.float64)
    frozen_positive = np.maximum(frozen_nonlinear, 0.0)
    frozen_gamma = np.asarray([row["frozen_initial_packet_positive_coercivity_ratio"] for row in history], dtype=np.float64)
    frozen_packets = np.asarray([row["frozen_initial_packet"] for row in history], dtype=np.float64)
    coercivity_windows: list[dict[str, float]] = []
    for index in range(1, len(history)):
        left, right = history[index - 1], history[index]
        duration = float(right["time"] - left["time"])
        positive_input = float(0.5 * duration * (
            max(float(left["frozen_initial_packet_nonlinear_rate"]), 0.0)
            + max(float(right["frozen_initial_packet_nonlinear_rate"]), 0.0)
        ))
        viscous_loss = float(0.5 * duration * (
            float(left["frozen_initial_packet_viscous_rate"])
            + float(right["frozen_initial_packet_viscous_rate"])
        ))
        coercivity_windows.append({
            "start_time": float(left["time"]),
            "end_time": float(right["time"]),
            "positive_nonlinear_input": positive_input,
            "viscous_loss": viscous_loss,
            "positive_coercivity_ratio": positive_input / viscous_loss if viscous_loss > 1.0e-30 else math.nan,
        })
    below_one = np.flatnonzero(frozen_gamma <= 1.0)
    first_below_one = (float(times[int(below_one[0])]) if len(below_one) else None)
    packet_peak = int(np.argmax(frozen_packets))
    below_one_after_peak = np.flatnonzero((np.arange(len(frozen_gamma)) > packet_peak) & (frozen_gamma <= 1.0))
    first_below_one_after_peak = (
        float(times[int(below_one_after_peak[0])]) if len(below_one_after_peak) else None
    )
    return {
        "contract": "finite-Galerkin normalized-profile parabolic-window receipt; no profile-uniform inference",
        "nominal_window_time": nominal_time,
        "actual_window_time": actual_time,
        "steps": steps,
        "checkpoint_fractions_requested": checkpoint_fractions,
        "mechanism_trace_count_requested": args.mechanism_trace_count,
        "mechanism_trace_start_fraction_requested": args.mechanism_trace_start_fraction,
        "mechanism_trace_end_fraction_requested": args.mechanism_trace_end_fraction,
        "mechanism_trace_contract": (
            "fine frozen-packet rate and shape telemetry; optional oriented convolution-atom coherence is sampled at "
            "the same checkpoints. Coarse interaction sampling is retained only at the two endpoints and must not be "
            "interpreted as a fine turnover trace"
        ),
        "backend": args.backend,
        "moving_packet_recurrence_ratio": endpoint["moving_packet"] / initial_row["moving_packet"],
        "moving_packet_heat_compensated_ratio": endpoint["moving_packet"] / endpoint["heat_moving_packet_exact_spectrum"],
        "moving_packet_scale_displacement": endpoint["dominant_shell"] - initial_row["dominant_shell"],
        "frozen_initial_packet_shell": frozen_centre,
        "frozen_initial_packet_recurrence_ratio": endpoint["frozen_initial_packet"] / initial_row["frozen_initial_packet"],
        "frozen_initial_packet_heat_compensated_ratio": (
            endpoint["frozen_initial_packet"] / endpoint["heat_frozen_initial_packet_exact_spectrum"]
        ),
        "frozen_initial_packet_heat_recurrence_ratio": (
            endpoint["heat_frozen_initial_packet_exact_spectrum"] / initial_row["frozen_initial_packet"]
        ),
        "integrated_target_nonlinear_input": float(np.trapezoid(target_nonlinear, times)),
        "integrated_target_positive_nonlinear_input": float(np.trapezoid(np.maximum(target_nonlinear, 0.0), times)),
        "integrated_target_viscous_loss": float(np.trapezoid(target_viscous, times)),
        "integrated_moving_packet_nonlinear_input": float(np.trapezoid(moving_nonlinear, times)),
        "integrated_moving_packet_positive_nonlinear_input": float(np.trapezoid(np.maximum(moving_nonlinear, 0.0), times)),
        "integrated_moving_packet_viscous_loss": float(np.trapezoid(moving_viscous, times)),
        "integrated_frozen_initial_packet_nonlinear_input": float(np.trapezoid(frozen_nonlinear, times)),
        "integrated_frozen_initial_packet_positive_nonlinear_input": float(np.trapezoid(np.maximum(frozen_nonlinear, 0.0), times)),
        "integrated_frozen_initial_packet_viscous_loss": float(np.trapezoid(frozen_viscous, times)),
        "integrated_frozen_initial_packet_positive_coercivity_ratio": (
            float(np.trapezoid(frozen_positive, times) / np.trapezoid(frozen_viscous, times))
            if float(np.trapezoid(frozen_viscous, times)) > 1.0e-30 else math.nan
        ),
        "frozen_initial_packet_positive_coercivity_ratio_sample_max": float(np.nanmax(frozen_gamma)),
        "frozen_initial_packet_positive_coercivity_ratio_sample_min": float(np.nanmin(frozen_gamma)),
        "frozen_initial_packet_first_sampled_time_gamma_at_most_one": first_below_one,
        "frozen_initial_packet_first_sampled_time_gamma_at_most_one_after_packet_peak": first_below_one_after_peak,
        "frozen_initial_packet_peak_sample_time": float(times[packet_peak]),
        "frozen_initial_packet_peak_sample_value": float(frozen_packets[packet_peak]),
        "frozen_packet_coercivity_windows": coercivity_windows,
        "packet_centre_changes_at_checkpoints": int(sum(
            row["dominant_shell"] != initial_row["dominant_shell"] for row in history[1:]
        )),
        "checkpoint_recentering_jump_sum": float(np.sum(recentering_jumps[1:])),
        "switching_warning": (
            "moving-packet rates are evaluated in a re-centred window. Frozen-initial-packet rates are the promotion authority; "
            "checkpoint_recentering_jump_sum is diagnostic only and is not an exact all-step switching balance."
        ),
        "coarse_interaction_hellinger_squared_initial_to_endpoint": hellinger_squared(
            coarse_distribution(initial_coarse), coarse_distribution(endpoint_coarse)
        ),
        "checkpoints": history,
        "coarse_interaction_initial": initial_coarse,
        "coarse_interaction_endpoint": endpoint_coarse,
        "_final_raw": final_raw,
    }


def shell_offset(radius: np.ndarray, target_shell: int) -> np.ndarray:
    return np.clip(np.floor(np.log2(np.maximum(radius, 1.0e-30))).astype(int) - target_shell, -5, 5)


def stratum_codes(p_wave: np.ndarray, q_wave: np.ndarray, target_shell: int,
                  output_helicity: int, p_helicity: np.ndarray, q_helicity: np.ndarray) -> np.ndarray:
    p_norm = np.linalg.norm(p_wave, axis=1)
    q_norm = np.linalg.norm(q_wave, axis=1)
    cosine = np.sum(p_wave * q_wave, axis=1) / np.maximum(p_norm * q_norm, 1.0e-30)
    angle = np.clip(((np.clip(cosine, -1.0, 1.0) + 1.0) * 4.0).astype(int), 0, 7)
    locality = np.clip(np.floor(np.log2(np.maximum(p_norm, q_norm) / np.maximum(np.minimum(p_norm, q_norm), 1.0))).astype(int), 0, 4)
    return np.stack((shell_offset(p_norm, target_shell), shell_offset(q_norm, target_shell), angle, locality,
                     np.full_like(angle, output_helicity), p_helicity, q_helicity), axis=1)


def coarse_helicity_labels(field_hat: np.ndarray, wave: np.ndarray) -> np.ndarray:
    """Classify each Fourier mode as plus, mixed, minus, or zero.

    This is a state-dependent coarse pushforward label, not a Waleffe transfer
    class.  ``0`` means either zero mode/negligible amplitude or neither
    helical energy exceeds the other by the declared 20% margin.
    """
    labels = np.zeros(field_hat.shape[1:], dtype=np.int8)
    for zyx in np.ndindex(labels.shape):
        mode = tuple(int(round(value)) for value in wave[(slice(None),) + zyx])
        if mode == (0, 0, 0):
            continue
        h_plus, h_minus = helical_basis(mode)
        value = field_hat[(slice(None),) + zyx]
        plus = float(abs(np.vdot(h_plus, value)) ** 2)
        minus = float(abs(np.vdot(h_minus, value)) ** 2)
        total = plus + minus
        if total <= 1.0e-30:
            continue
        imbalance = (plus - minus) / total
        labels[zyx] = 1 if imbalance >= 0.2 else (-1 if imbalance <= -0.2 else 0)
    return labels


def pair_contributions(field_flat: np.ndarray, wave_flat: np.ndarray, output_flat: int,
                       p_index: np.ndarray, q_index: np.ndarray, target_shell: int) -> np.ndarray:
    up, uq = field_flat[:, p_index], field_flat[:, q_index]
    kp, kq = wave_flat[:, p_index], wave_flat[:, q_index]
    pair = -1j * np.sum(kq * up, axis=0)[None, :] * uq - 1j * np.sum(kp * uq, axis=0)[None, :] * up
    diagonal = p_index == q_index
    pair[:, diagonal] = (-1j * np.sum(kq[:, diagonal] * up[:, diagonal], axis=0)[None, :]
                         * uq[:, diagonal])
    output_wave = wave_flat[:, output_flat]
    norm_sq = float(np.dot(output_wave, output_wave))
    if norm_sq > 0.0:
        pair -= output_wave[:, None] * (np.sum(output_wave[:, None] * pair, axis=0) / norm_sq)[None, :]
    return 2.0 * (2 ** target_shell) * np.real(np.sum(np.conjugate(field_flat[:, output_flat])[:, None] * pair, axis=0))


def stratified_interaction_estimate(args: argparse.Namespace, field_hat: np.ndarray,
                                    nonlinear_hat: np.ndarray, wave: np.ndarray, norm: np.ndarray,
                                    rng: np.random.Generator) -> dict[str, Any]:
    """Estimate absolute interaction mass for selected outputs by finite strata.

    Each stratum is an exact finite collection of canonical unordered input
    pairs.  Sampling is with replacement, so population-size times the sample
    mean is unbiased and the reported standard error is explicit.
    """
    n = args.n
    lower, upper = float(2 ** args.target_shell), float(2 ** (args.target_shell + 1))
    shell_flat = np.flatnonzero(((norm >= lower) & (norm < upper)).ravel())
    modal_rate = 2.0 * (2 ** args.target_shell) * np.real(np.sum(np.conjugate(field_hat) * nonlinear_hat, axis=0)).ravel()
    activity = np.abs(modal_rate[shell_flat])
    sorted_outputs = shell_flat[np.argsort(activity)[::-1]]
    requested_count = min(args.output_modes, len(shell_flat))
    if args.output_activity_coverage > 0.0 and float(np.sum(activity)) > 1.0e-30:
        coverage_count = int(np.searchsorted(
            np.cumsum(activity[np.argsort(activity)[::-1]]),
            args.output_activity_coverage * float(np.sum(activity)), side="left"
        ) + 1)
        requested_count = max(requested_count, coverage_count)
    chosen = sorted_outputs[:requested_count]
    full_output_activity = float(np.sum(activity))
    selected_output_activity = float(np.sum(np.abs(modal_rate[chosen])))
    grid = np.arange(n ** 3, dtype=np.int64)
    coordinates = np.column_stack(np.unravel_index(grid, (n, n, n)))
    field_flat = field_hat.reshape(3, -1)
    wave_flat = wave.reshape(3, -1)
    helicity_flat = coarse_helicity_labels(field_hat, wave).ravel()
    aggregates: dict[tuple[int, ...], dict[str, float]] = defaultdict(lambda: {"population": 0.0, "estimate": 0.0, "variance": 0.0, "samples": 0.0})
    total_estimate = 0.0
    total_variance = 0.0
    exact_total = 0.0
    for output_flat in chosen:
        output_coords = np.asarray(np.unravel_index(int(output_flat), (n, n, n)), dtype=np.int64)
        q_coords = (output_coords[None, :] - coordinates) % n
        q_flat = np.ravel_multi_index(q_coords.T, (n, n, n))
        canonical = grid <= q_flat
        p = grid[canonical]
        q = q_flat[canonical]
        if args.exact_check:
            exact_total += float(np.sum(np.abs(pair_contributions(
                field_flat, wave_flat, int(output_flat), p, q, args.target_shell
            ))))
        output_helicity = int(helicity_flat[int(output_flat)])
        codes = stratum_codes(wave_flat[:, p].T, wave_flat[:, q].T, args.target_shell,
                              output_helicity, helicity_flat[p], helicity_flat[q])
        packed = (codes[:, 0] + 11 * (codes[:, 1] + 11 * (codes[:, 2] + 8 * (
            codes[:, 3] + 5 * ((codes[:, 4] + 1) + 3 * ((codes[:, 5] + 1) + 3 * (codes[:, 6] + 1)))
        ))))
        for identifier in np.unique(packed):
            positions = np.flatnonzero(packed == identifier)
            population = int(positions.size)
            draw_count = min(args.samples_per_stratum, max(1, population))
            draw = positions[rng.integers(0, population, size=draw_count)]
            values = np.abs(pair_contributions(field_flat, wave_flat, int(output_flat), p[draw], q[draw], args.target_shell))
            estimate = float(population * np.mean(values))
            variance = float(population ** 2 * np.var(values, ddof=1) / draw_count) if draw_count > 1 else math.nan
            code = tuple(int(value) for value in codes[positions[0]])
            row = aggregates[code]
            row["population"] += population
            row["estimate"] += estimate
            row["samples"] += draw_count
            if math.isfinite(variance):
                row["variance"] += variance
                total_variance += variance
            total_estimate += estimate
    strata = [
        {"shell_offset_left": code[0], "shell_offset_right": code[1], "angle_bin": code[2], "locality_log2_bin": code[3],
         "helicity_output": code[4], "helicity_left": code[5], "helicity_right": code[6],
         "population": int(row["population"]), "samples": int(row["samples"]), "absolute_activity_estimate": row["estimate"],
         "standard_error": math.sqrt(row["variance"]) if row["variance"] >= 0.0 else None}
        for code, row in sorted(aggregates.items(), key=lambda item: item[1]["estimate"], reverse=True)
    ]
    result = {
        "contract": "finite-stratum uniformly sampled absolute interaction aggregate; no entropy estimator or continuum claim",
        "selected_output_mode_count": int(len(chosen)),
        "selected_output_modal_activity_capture": (selected_output_activity / full_output_activity if full_output_activity > 1.0e-30 else math.nan),
        "absolute_activity_estimate": total_estimate,
        "standard_error_independent_strata": math.sqrt(total_variance),
        "nominal_95_percent_interval": [max(0.0, total_estimate - 1.96 * math.sqrt(total_variance)), total_estimate + 1.96 * math.sqrt(total_variance)],
        "strata": strata,
        "warning": "normal-approximation interval accounts only for within-stratum Monte Carlo variance; it is not a certified enclosure",
    }
    if args.exact_check:
        result["exact_selected_carrier_absolute_activity"] = exact_total
        result["estimator_relative_error_against_exact_selected_carrier"] = (
            (total_estimate - exact_total) / exact_total if exact_total > 1.0e-30 else math.nan
        )
    return result


def main() -> None:
    args = parse_args()
    if (args.n < 12 or args.nu <= 0.0 or args.critical_mass <= 0.0 or args.chi_attempts <= 0
            or args.dt <= 0.0 or args.window_c <= 0.0 or args.moving_packet_radius < 0
            or args.mechanism_trace_count < 0 or args.triad_coherence_samples_per_output < 0
            or args.canonical_triad_samples_per_output < 0
            or args.triad_coherence_batch_size <= 0):
        raise ValueError("n >= 12, nonnegative packet radius/trace count, and positive nu/mass/attempts/dt/window-c are required")
    if not (0.0 <= args.mechanism_trace_start_fraction < args.mechanism_trace_end_fraction <= 1.0):
        raise ValueError("mechanism trace fractions must satisfy 0 <= start < end <= 1")
    if args.require_chi_tolerance and args.chi_target is None:
        raise ValueError("--require-chi-tolerance requires --chi-target")
    if args.state_perturbation != "none" and args.state_input is None:
        raise ValueError("--state-perturbation requires --state-input")
    if not (0.0 < args.angular_width <= math.pi and args.radial_log_width > 0.0
            and -1.0 <= args.helicity_bias <= 1.0 and 0.0 <= args.spatial_coherence <= 1.0):
        raise ValueError("invalid profile-shape coordinate range")
    if not (0.0 <= args.target_dominance_min <= 1.0 and 0.0 <= args.output_activity_coverage <= 1.0):
        raise ValueError("target dominance and output activity coverage must lie in [0,1]")
    if args.selection_objective == "short-survival" and not args.evolve:
        raise ValueError("--selection-objective short-survival requires --evolve")
    wave, norm = frequency_grid(args.n)
    norm_sq = norm ** 2
    candidates: list[tuple[float, int, np.ndarray, np.ndarray, dict[str, float], np.ndarray]] = []
    if args.state_input is not None:
        with np.load(args.state_input) as state:
            raw = np.asarray(state["raw_hat"], dtype=np.complex128)
            attempt = int(state.get("selected_attempt", 0))
        if raw.shape != (args.n, args.n, args.n, 3):
            raise ValueError(f"state shape {raw.shape} does not match N={args.n}")
        raw = perturb_saved_state(args, raw)
        field = raw_to_field_hat(raw, wave, norm_sq)
        nonlinear, metrics = static_metrics(args, field, wave, norm, norm_sq)
        signed = float(metrics["chi_signed"])
        if (not args.continuation_state
                and ((args.chi_sign == "positive" and signed <= 0.0)
                     or (args.chi_sign == "negative" and signed >= 0.0))):
            raise RuntimeError("loaded state does not meet the requested signed-chi convention")
        matched_chi = abs(signed) if args.chi_sign == "absolute" else (signed if args.chi_sign == "positive" else -signed)
        mismatch = abs(matched_chi - args.chi_target) if args.chi_target is not None else 0.0
        if args.require_chi_tolerance and mismatch > args.chi_tolerance:
            raise RuntimeError("loaded/perturbed state misses the requested signed-chi tolerance")
        metrics["chi_matching_value"] = matched_chi
        metrics["chi_matching_convention"] = args.chi_sign
        if (not args.continuation_state
                and metrics["target_packet_dominance"] < args.target_dominance_min):
            raise RuntimeError("loaded state does not meet target-dominance admissibility")
        candidates.append((mismatch, attempt, raw, field, metrics, nonlinear))
    else:
        for attempt in range(args.chi_attempts):
            raw = profile_raw_hat(args, args.seed + attempt)
            field = raw_to_field_hat(raw, wave, norm_sq)
            nonlinear, metrics = static_metrics(args, field, wave, norm, norm_sq)
            signed = float(metrics["chi_signed"])
            if args.chi_sign == "positive" and signed <= 0.0:
                continue
            if args.chi_sign == "negative" and signed >= 0.0:
                continue
            matched_chi = abs(signed) if args.chi_sign == "absolute" else (signed if args.chi_sign == "positive" else -signed)
            mismatch = abs(matched_chi - args.chi_target) if args.chi_target is not None else 0.0
            if args.require_chi_tolerance and mismatch > args.chi_tolerance:
                continue
            metrics["chi_matching_value"] = matched_chi
            metrics["chi_matching_convention"] = args.chi_sign
            if metrics["target_packet_dominance"] < args.target_dominance_min:
                continue
            candidates.append((mismatch, attempt, raw, field, metrics, nonlinear))
    if not candidates:
        raise RuntimeError("no phase trial met the signed-chi and target-dominance admissibility slice")
    selected_evolution: dict[str, Any] | None = None
    survival_scores: list[dict[str, Any]] = []
    selection_status = "chi_match"
    if args.selection_objective == "short-survival":
        survivors: list[tuple[float, float, tuple[float, int, np.ndarray, np.ndarray, dict[str, float], np.ndarray], dict[str, Any]]] = []
        trial_records: list[tuple[float, float, tuple[float, int, np.ndarray, np.ndarray, dict[str, float], np.ndarray], dict[str, Any]]] = []
        for ordinal, candidate in enumerate(candidates, start=1):
            print(
                f"short-survival trial {ordinal}/{len(candidates)} attempt={candidate[1]} "
                f"chi={candidate[4]['chi_signed']:.8g}",
                file=sys.stderr,
                flush=True,
            )
            evolution = evolve_profile(args, candidate[2], wave, norm, norm_sq)
            integrated_input = float(evolution["integrated_frozen_initial_packet_nonlinear_input"])
            score = float(evolution["moving_packet_recurrence_ratio"])
            survival_scores.append({
                "attempt": candidate[1], "chi_mismatch": candidate[0], "moving_packet_recurrence_ratio": score,
                "integrated_frozen_initial_packet_nonlinear_input": integrated_input,
                "integrated_moving_packet_nonlinear_input": float(evolution["integrated_moving_packet_nonlinear_input"]),
                "accepted_positive_frozen_initial_packet_input": integrated_input > 0.0,
            })
            if not args.require_positive_short_input or integrated_input > 0.0:
                survivors.append((score, -candidate[0], candidate, evolution))
            trial_records.append((score, -candidate[0], candidate, evolution))
            print(
                f"short-survival trial {ordinal}/{len(candidates)} Rmove={score:.8g} "
                f"frozen_integrated_input={integrated_input:.8g}",
                file=sys.stderr,
                flush=True,
            )
        if not survivors:
            # Keep the best rejected trajectory as a receipt: failure of a
            # promotion gate is data, not grounds for deleting the screen.
            selection_status = "no_trial_met_positive_frozen_initial_packet_input_gate"
            selected_trial = max(trial_records, key=lambda row: (row[0], row[1]))
            _, _, selected, selected_evolution = selected_trial
        else:
            _, _, selected, selected_evolution = max(survivors, key=lambda row: (row[0], row[1]))
        mismatch, attempt, raw, field, static, nonlinear = selected
    else:
        mismatch, attempt, raw, field, static, nonlinear = min(candidates, key=lambda row: row[0])
    shape = profile_shape_metrics(field, wave, norm)
    estimate = stratified_interaction_estimate(args, field, nonlinear, wave, norm, np.random.default_rng(args.seed + 1000003))
    payload = {
        "contract": "ns_normalized_profile_quotient_audit_nonpromoting",
        "authority": authority(),
        "inputs": {
            "n": args.n, "nu": args.nu, "target_shell": args.target_shell, "critical_mass": args.critical_mass,
            "angular_width": args.angular_width, "radial_log_width": args.radial_log_width,
            "helicity_bias": args.helicity_bias, "spatial_coherence": args.spatial_coherence,
            "angular_axis": list(args.angular_axis), "seed": args.seed,
            "state_input": str(args.state_input) if args.state_input is not None else None,
            "state_perturbation": args.state_perturbation,
            "perturb_epsilon": args.perturb_epsilon,
            "perturb_seed": args.perturb_seed,
            "chi_target": args.chi_target, "chi_sign": args.chi_sign, "chi_attempts": args.chi_attempts,
            "chi_tolerance": args.chi_tolerance, "require_chi_tolerance": args.require_chi_tolerance,
            "target_dominance_min": args.target_dominance_min,
            "checkpoint_fractions": args.checkpoint_fractions,
            "mechanism_trace_count": args.mechanism_trace_count,
            "mechanism_trace_start_fraction": args.mechanism_trace_start_fraction,
            "mechanism_trace_end_fraction": args.mechanism_trace_end_fraction,
            "triad_coherence_samples_per_output": args.triad_coherence_samples_per_output,
            "canonical_triad_samples_per_output": args.canonical_triad_samples_per_output,
            "triad_coherence_batch_size": args.triad_coherence_batch_size,
            "selection_objective": args.selection_objective,
            "require_positive_short_input": args.require_positive_short_input,
        },
        "quotient_slice": {
            "translation_fixed": "origin-centred phase convention",
            "amplitude_fixed": "finite dyadic H^(1/2) mass exactly normalised",
            "dyadic_scale_status": "target shell declared; literal scale copies are not interpreted as new profile directions",
            "chi_match_attempt": attempt,
            "chi_absolute_mismatch": mismatch,
            "chi_match_within_requested_tolerance": (mismatch <= args.chi_tolerance if args.chi_target is not None else None),
            "candidate_count_after_signed_chi_and_tightness_filter": len(candidates),
            "short_survival_screen": survival_scores if survival_scores else None,
            "selection_status": selection_status,
            "warning": "critical mass and chi cannot both be imposed by a single scalar rescaling at fixed carrier scale; chi is matched by profile/phase selection",
            "perturbation_contract": (
                "state-anchored finite local deformation followed by exact finite critical-mass normalisation; "
                "admissibility is checked after perturbation"
                if args.state_perturbation != "none" else None
            ),
        },
        "shape_metrics": shape,
        "static_packet_metrics": static,
        "stratified_interaction_measure": estimate,
    }
    if args.evolve:
        evolution_payload = selected_evolution or evolve_profile(args, raw, wave, norm, norm_sq)
        final_raw = np.asarray(evolution_payload.pop("_final_raw"), dtype=np.complex128)
        payload["finite_galerkin_evolution"] = evolution_payload
    if args.save_selected_state is not None:
        args.save_selected_state.parent.mkdir(parents=True, exist_ok=True)
        np.savez_compressed(
            args.save_selected_state,
            raw_hat=raw,
            selected_attempt=np.asarray(attempt, dtype=np.int64),
            seed=np.asarray(args.seed + attempt, dtype=np.int64),
            critical_mass=np.asarray(args.critical_mass, dtype=np.float64),
            chi_signed=np.asarray(static["chi_signed"], dtype=np.float64),
        )
        payload["selected_state_receipt"] = {
            "path": str(args.save_selected_state),
            "format": "npz-compressed raw FFT coefficients; preserves the exact selected finite state",
            "attempt": attempt,
            "effective_seed": args.seed + attempt,
        }
    if args.save_final_state is not None:
        if not args.evolve:
            raise ValueError("--save-final-state requires --evolve")
        args.save_final_state.parent.mkdir(parents=True, exist_ok=True)
        np.savez_compressed(
            args.save_final_state,
            raw_hat=final_raw,
            segment_window_c=np.asarray(args.window_c, dtype=np.float64),
            dt=np.asarray(args.dt, dtype=np.float64),
            nu=np.asarray(args.nu, dtype=np.float64),
        )
        payload["final_state_receipt"] = {
            "path": str(args.save_final_state),
            "format": "npz-compressed raw FFT coefficients after the declared finite-Galerkin segment",
            "segment_window_c": args.window_c,
        }
    write_json_atomically(args.output_json, payload)
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
