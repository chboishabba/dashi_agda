#!/usr/bin/env python3
"""Run a constrained adversarial K_N(A) fork search on NS shell carriers.

This is a candidate-only numerical harness. It uses the same positive-subspace
operator convention as ``ns_triad_kn_exact_identity_scan.py``:

    K_N(A) = L_abs(A)^(-1/2) L_neg(A) L_abs(A)^(-1/2)

The search is deliberately fail-closed. It reports the best sampled feasible
candidate for each shell cutoff, and it separately flags any sampled
low-frame/high-radial-band/low-dissipation unresolved-danger row. The older
angular N_eff diagnostic is retained, but it is not treated as radial
bandwidth. No theorem, full-NS, or Clay promotion follows from this surface.
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any

import numpy as np

from ns_boundary_pressure_gate_scan import _frame_indices  # type: ignore
from ns_triad_cocycle_floor_scan import _validate_shells  # type: ignore
from ns_triad_frame_stability_scan import (  # type: ignore
    AUTHORITY,
    DEFAULT_POOL_MULTIPLIER,
    DEFAULT_RAW_ARCHIVE,
    DEFAULT_TOP_K,
    DEFAULT_ZERO_EPS,
    ERROR_STATUS,
    OK_STATUS,
    PARTIAL_STATUS,
    _build_frame_surface,
    _frame_velocity,
    _json_text,
    _load_raw_bundle,
    _scalar_vorticity_spectrum,
)
from ns_orbit_phase_coherence_scan import ModeRecord  # type: ignore


SCRIPT_NAME = "scripts/ns_triad_constrained_adversarial_fork_optimizer.py"
CONTRACT = "ns_triad_constrained_adversarial_fork_optimizer"
ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_CONSTRAINED_ADVERSARIAL_FORK_OPTIMIZER"
SCHEMA_VERSION = "1.0.0"

DEFAULT_OUTPUT_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_constrained_adversarial_fork_optimizer_N128_20260623.json"
)
DEFAULT_SHELLS = (2, 3, 4, 5)
DEFAULT_SAMPLE_COUNT = 384
DEFAULT_MIX_COUNT = 12
DEFAULT_SEEDS = (0, 1, 2, 3, 5, 8)
DEFAULT_C0 = 0.25
DEFAULT_N0 = 1.5
DEFAULT_D0 = 3.0
DEFAULT_R0 = 1.5
DEFAULT_HIGH_SHELL_CUTOFF = 2.0
DEFAULT_HIGH_SHELL_ETA = 0.10
TAIL_MASS_CUTOFFS = (2, 3, 4, 5)

CONTROL_CARD = {
    "O": "Search the finite-dimensional no-triple-danger fork on genuine NS shell-carrier telemetry.",
    "R": (
        "For shell cutoffs N=2..5, sample energy-normalized amplitude profiles A, build K_N(A), "
        "and minimize lambda_min under radial_effective_scale >= R0 or high-shell mass >= eta, "
        "with D <= D0. Angular N_eff is diagnostic, not the bandwidth variable."
    ),
    "C": SCRIPT_NAME,
    "S": "Candidate-only finite-dimensional telemetry; the optimizer is sampled and non-promoting.",
    "L": (
        "Load the raw N128 velocity archive, build Fourier-vorticity triad carriers, sample adversarial "
        "amplitude profiles, evaluate K_N(A), angular N_eff, radial scale, high-shell mass, "
        "dissipation, BKM proxy, product separation, and worst eigenvector shell localization."
    ),
    "P": ROUTE_DECISION,
    "G": "No theorem, full-NS, or Clay promotion is inferred from this scan.",
    "F": (
        "This narrows the finite-dimensional fork target only; analytic radial no-triple-danger, "
        "Schur/frame gap, determinant growth, rarity, and PDE residence-time exclusion remain open."
    ),
}


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--raw-archive", type=Path, default=DEFAULT_RAW_ARCHIVE)
    parser.add_argument("--output-json", type=Path, default=DEFAULT_OUTPUT_JSON)
    parser.add_argument("--frame", type=int, default=None)
    parser.add_argument("--frame-limit", type=int, default=1)
    parser.add_argument("--top-k", type=int, default=DEFAULT_TOP_K)
    parser.add_argument("--pool-multiplier", type=int, default=DEFAULT_POOL_MULTIPLIER)
    parser.add_argument("--zero-eps", type=float, default=DEFAULT_ZERO_EPS)
    parser.add_argument("--sample-count", type=int, default=DEFAULT_SAMPLE_COUNT)
    parser.add_argument("--mix-count", type=int, default=DEFAULT_MIX_COUNT)
    parser.add_argument("--profile-sample-limit", type=int, default=18)
    parser.add_argument("--seed", dest="seeds", action="append", type=int, default=None)
    parser.add_argument("--c0", type=float, default=DEFAULT_C0)
    parser.add_argument("--n0", type=float, default=DEFAULT_N0)
    parser.add_argument("--d0", type=float, default=DEFAULT_D0)
    parser.add_argument("--r0", type=float, default=DEFAULT_R0)
    parser.add_argument("--high-shell-cutoff", type=float, default=DEFAULT_HIGH_SHELL_CUTOFF)
    parser.add_argument("--high-shell-eta", type=float, default=DEFAULT_HIGH_SHELL_ETA)
    parser.add_argument(
        "--shell",
        dest="shells",
        action="append",
        type=int,
        default=None,
        help="Shell cutoff N to evaluate; may be repeated. Defaults to 2,3,4,5.",
    )
    parser.add_argument("--pretty", action="store_true")
    return parser.parse_args()


def _laplacian(adjacency: np.ndarray) -> np.ndarray:
    degree = np.sum(adjacency, axis=1)
    return 0.5 * (np.diag(degree) - adjacency + (np.diag(degree) - adjacency).T)


def _positive_subspace(matrix: np.ndarray, tol: float) -> tuple[np.ndarray, np.ndarray]:
    evals, evecs = np.linalg.eigh(0.5 * (matrix + matrix.T))
    mask = np.asarray(evals > tol, dtype=bool)
    return np.asarray(evals[mask], dtype=np.float64), np.asarray(evecs[:, mask], dtype=np.float64)


def _sqrt_pinv(evals: np.ndarray, basis: np.ndarray) -> np.ndarray:
    if len(evals) == 0:
        return np.zeros((basis.shape[0], basis.shape[0]), dtype=np.float64)
    scales = np.asarray([1.0 / math.sqrt(float(value)) for value in evals], dtype=np.float64)
    return (basis * scales) @ basis.T


def _shell_levels(shell_radii: np.ndarray) -> np.ndarray:
    unique = sorted({float(value) for value in shell_radii})
    rank = {value: index + 1 for index, value in enumerate(unique)}
    return np.asarray([float(rank[float(value)]) for value in shell_radii], dtype=np.float64)


def _integer_modes(n: int) -> np.ndarray:
    raw = np.fft.fftfreq(n) * float(n)
    return np.asarray(np.rint(raw), dtype=np.int64)


def _cube_modes(spectrum: np.ndarray, shell_n: int, zero_eps: float) -> list[ModeRecord]:
    n = int(spectrum.shape[0])
    integer = _integer_modes(n)
    modes: list[ModeRecord] = []
    cutoff = int(shell_n)
    for i, kx in enumerate(integer):
        if abs(int(kx)) > cutoff:
            continue
        for j, ky in enumerate(integer):
            if abs(int(ky)) > cutoff:
                continue
            for k, kz in enumerate(integer):
                key = (int(kx), int(ky), int(kz))
                if key == (0, 0, 0) or max(abs(key[0]), abs(key[1]), abs(key[2])) > cutoff:
                    continue
                value = complex(spectrum[i, j, k])
                amp = float(abs(value))
                if not math.isfinite(amp) or amp <= float(zero_eps):
                    amp = float(zero_eps)
                modes.append(
                    ModeRecord(
                        key=key,
                        amplitude=amp,
                        phase=float(math.atan2(value.imag, value.real)),
                        shell_radius=float(max(abs(key[0]), abs(key[1]), abs(key[2]))),
                    )
                )
    return modes


def _profile_metrics(
    probability: np.ndarray,
    shell_levels: np.ndarray,
    zero_eps: float,
    high_shell_cutoff: float,
) -> dict[str, float]:
    p = np.asarray(probability, dtype=np.float64)
    shells = np.asarray(shell_levels, dtype=np.float64)
    n_eff = 1.0 / max(float(np.sum(p * p)), float(zero_eps))
    dissipation = float(np.sum((shells * shells) * p))
    shell_mean = float(np.sum(shells * p))
    shell_variance = float(np.sum(((shells - shell_mean) ** 2) * p))
    radial_effective_scale = float(math.sqrt(max(dissipation, 0.0)))
    high_shell_mass = float(np.sum(p[shells >= float(high_shell_cutoff)]))
    high_shell_mass_by_cutoff = {
        str(int(cutoff)): float(np.sum(p[shells >= float(cutoff)]))
        for cutoff in TAIL_MASS_CUTOFFS
    }
    active = p > float(zero_eps)
    radial_shell_min = float(np.min(shells[active])) if np.any(active) else None
    radial_shell_max = float(np.max(shells[active])) if np.any(active) else None
    angular_mode_count = int(np.count_nonzero(active))
    positive_p = p[p > float(zero_eps)]
    entropy = float(-np.sum(positive_p * np.log(positive_p))) if len(positive_p) else 0.0
    bkm_proxy = float(np.sum(shells * np.sqrt(np.maximum(p, 0.0))))
    return {
        "energy": 1.0,
        "n_eff": float(n_eff),
        "angular_mode_count": float(angular_mode_count),
        "angular_entropy": entropy,
        "radial_shell_min": radial_shell_min,
        "radial_shell_max": radial_shell_max,
        "radial_shell_barycenter": shell_mean,
        "radial_shell_variance": shell_variance,
        "radial_effective_scale": radial_effective_scale,
        "high_shell_mass_fraction": high_shell_mass,
        "high_shell_mass_by_cutoff": high_shell_mass_by_cutoff,
        "dissipation_proxy": dissipation,
        "bkm_proxy": bkm_proxy,
    }


def _weighted_adjacencies(
    triads: list[Any],
    probability: np.ndarray,
    mode_count: int,
    zero_eps: float,
) -> tuple[np.ndarray, np.ndarray]:
    positive = np.zeros((mode_count, mode_count), dtype=np.float64)
    negative = np.zeros_like(positive)
    amplitude = np.sqrt(np.maximum(np.asarray(probability, dtype=np.float64), 0.0))
    for triad in triads:
        left = int(triad.left)
        right = int(triad.right)
        out = int(triad.out)
        raw_weight = float(amplitude[left] * amplitude[right] * amplitude[out])
        if not math.isfinite(raw_weight) or raw_weight <= float(zero_eps):
            continue
        pair_weight = raw_weight / 3.0
        positive_weight = pair_weight * max(float(triad.coherence), 0.0)
        negative_weight = pair_weight * max(-float(triad.coherence), 0.0)
        for a, b in ((left, right), (left, out), (right, out)):
            positive[a, b] += positive_weight
            positive[b, a] += positive_weight
            negative[a, b] += negative_weight
            negative[b, a] += negative_weight
    return positive, negative


def _evaluate_profile(
    triads: list[Any],
    probability: np.ndarray,
    shell_levels: np.ndarray,
    zero_eps: float,
    high_shell_cutoff: float,
) -> dict[str, Any]:
    mode_count = int(len(probability))
    positive_adj, negative_adj = _weighted_adjacencies(triads, probability, mode_count, zero_eps)
    abs_adj = positive_adj + negative_adj
    l_abs = _laplacian(abs_adj)
    l_neg = _laplacian(negative_adj)
    tol = max(float(zero_eps), 1.0e-10)
    evals, basis = _positive_subspace(l_abs, tol=tol)
    if len(evals) == 0:
        metrics = _profile_metrics(probability, shell_levels, zero_eps, high_shell_cutoff)
        return {
            **metrics,
            "status": PARTIAL_STATUS,
            "lambda_min_kn_a": None,
            "lambda_max_kn_a": None,
            "l_abs_positive_rank": 0,
            "worst_eigenvector_shell": None,
            "worst_eigenvector_shell_mass_fraction": None,
            "warnings": ["l_abs_has_no_positive_subspace"],
        }

    inv_sqrt = _sqrt_pinv(evals, basis)
    k_matrix = 0.5 * (inv_sqrt @ l_neg @ inv_sqrt + (inv_sqrt @ l_neg @ inv_sqrt).T)
    k_reduced = 0.5 * (basis.T @ k_matrix @ basis + (basis.T @ k_matrix @ basis).T)
    k_eigs, k_evecs = np.linalg.eigh(k_reduced)
    worst_index = int(np.argmin(k_eigs))
    full_vec = np.asarray(basis @ k_evecs[:, worst_index], dtype=np.float64)
    masses = full_vec * full_vec
    total_mass = float(np.sum(masses))
    shell_mass: dict[int, float] = {}
    for shell_value, mass in zip(shell_levels, masses, strict=False):
        shell = int(shell_value)
        shell_mass[shell] = shell_mass.get(shell, 0.0) + float(mass)
    worst_shell, worst_shell_mass = max(shell_mass.items(), key=lambda item: item[1]) if shell_mass else (0, 0.0)
    metrics = _profile_metrics(probability, shell_levels, zero_eps, high_shell_cutoff)
    return {
        **metrics,
        "status": OK_STATUS,
        "lambda_min_kn_a": float(np.min(k_eigs)),
        "lambda_max_kn_a": float(np.max(k_eigs)),
        "l_abs_positive_rank": int(len(evals)),
        "worst_eigenvector_shell": int(worst_shell),
        "worst_eigenvector_shell_mass_fraction": float(worst_shell_mass / max(total_mass, float(zero_eps))),
        "warnings": [],
    }


def _normalize_profile(weights: np.ndarray, zero_eps: float) -> np.ndarray:
    clipped = np.maximum(np.asarray(weights, dtype=np.float64), 0.0)
    total = float(np.sum(clipped))
    if not math.isfinite(total) or total <= float(zero_eps):
        clipped = np.ones_like(clipped, dtype=np.float64)
        total = float(np.sum(clipped))
    return clipped / total


def _candidate_profiles(
    base_probability: np.ndarray,
    shell_levels: np.ndarray,
    sample_count: int,
    mix_count: int,
    seed: int,
    zero_eps: float,
) -> list[tuple[str, np.ndarray]]:
    rng = np.random.default_rng(int(seed))
    count = max(0, int(sample_count))
    mode_count = int(len(base_probability))
    profiles: list[tuple[str, np.ndarray]] = [
        ("observed", _normalize_profile(base_probability, zero_eps)),
        ("uniform", np.full(mode_count, 1.0 / float(mode_count), dtype=np.float64)),
    ]

    low_mask = shell_levels <= min(shell_levels) + 1.0e-12
    low_reference: np.ndarray | None = None
    if np.any(low_mask):
        low = np.where(low_mask, 1.0, 0.0)
        low_reference = _normalize_profile(low, zero_eps)
        profiles.append(("lowest_shell_uniform", low_reference))

    next_mask = shell_levels >= min(shell_levels) + 1.0 - 1.0e-12
    next_mask &= shell_levels <= min(shell_levels) + 1.0 + 1.0e-12
    high_mask = shell_levels >= min(shell_levels) + 1.0 - 1.0e-12
    if low_reference is not None and np.any(next_mask):
        next_reference = _normalize_profile(np.where(next_mask, 1.0, 0.0), zero_eps)
        for high_mass in (0.10, 0.15, 0.25, 0.40, 0.55, 0.65):
            profiles.append(
                (
                    f"radial_low_d_shell2_mass_{high_mass:.2f}",
                    _normalize_profile((1.0 - high_mass) * low_reference + high_mass * next_reference, zero_eps),
                )
            )
    if low_reference is not None and np.any(high_mask):
        high_reference = _normalize_profile(np.where(high_mask, 1.0, 0.0), zero_eps)
        for high_mass in (0.10, 0.15, 0.25, 0.40):
            profiles.append(
                (
                    f"radial_spread_low_d_high_mass_{high_mass:.2f}",
                    _normalize_profile((1.0 - high_mass) * low_reference + high_mass * high_reference, zero_eps),
                )
            )

    alphas = np.linspace(0.0, 1.0, num=max(0, int(mix_count)))
    low_reference = low_reference if low_reference is not None else profiles[-1][1]
    for alpha in alphas:
        profiles.append((f"observed_low_mix_{alpha:.3f}", _normalize_profile((1.0 - alpha) * base_probability + alpha * low_reference, zero_eps)))

    alpha_values = (0.15, 0.35, 0.75, 1.5, 3.0)
    for index in range(count):
        concentration = alpha_values[index % len(alpha_values)]
        draw = rng.dirichlet(np.full(mode_count, concentration, dtype=np.float64))
        if index % 3 == 0:
            shell_bias = np.exp(-0.65 * (shell_levels - float(np.min(shell_levels))))
            draw = _normalize_profile(draw * shell_bias, zero_eps)
        elif index % 3 == 1:
            draw = _normalize_profile(0.5 * draw + 0.5 * base_probability, zero_eps)
        profiles.append((f"seed{seed}_sample{index:04d}", draw))
    return profiles


def _branch(row: dict[str, Any], c0: float, r0: float, high_shell_eta: float, d0: float) -> str:
    lmin = row.get("lambda_min_kn_a")
    if not isinstance(lmin, (int, float)) or not math.isfinite(float(lmin)):
        return "unavailable"
    if float(lmin) >= float(c0):
        return "frame-coercive"
    radial_high = (
        float(row["radial_effective_scale"]) >= float(r0)
        or float(row["high_shell_mass_fraction"]) >= float(high_shell_eta)
    )
    if not radial_high:
        return "low-radial-band"
    if float(row["dissipation_proxy"]) > float(d0):
        return "high-dissipation"
    return "unresolved-danger"


def _row(
    slot: int,
    snapshot: int,
    bundle: Any,
    shell_n: int,
    top_k: int,
    pool_multiplier: int,
    zero_eps: float,
    sample_count: int,
    mix_count: int,
    seeds: list[int],
    c0: float,
    n0: float,
    d0: float,
    r0: float,
    high_shell_cutoff: float,
    high_shell_eta: float,
    profile_sample_limit: int,
) -> dict[str, Any]:
    row: dict[str, Any] = {
        "frame": int(slot),
        "snapshot_index": int(snapshot),
        "shell": int(shell_n),
        "source": str(bundle.path),
        "candidate_only": True,
        "empirical_non_promoting": True,
        "fail_closed": True,
        "top_k": int(top_k),
        "sample_count_per_seed": int(sample_count),
        "mix_count_per_seed": int(mix_count),
        "seed_count": int(len(seeds)),
        "profile_sample_limit": int(profile_sample_limit),
        "radial_r0": float(r0),
        "high_shell_cutoff": float(high_shell_cutoff),
        "high_shell_eta": float(high_shell_eta),
    }
    try:
        u, v, w = _frame_velocity(bundle, snapshot)
        spectrum = _scalar_vorticity_spectrum(u, v, w, bundle.domain_length)
        shell_modes = _cube_modes(spectrum, shell_n=shell_n, zero_eps=zero_eps)
        triads, frame_metrics = _build_frame_surface(shell_modes, zero_eps=zero_eps, triad_sample_limit=8)
    except Exception as exc:  # noqa: BLE001
        row["status"] = ERROR_STATUS
        row["errors"] = [f"constrained_adversarial_optimizer_error: {exc}"]
        return row

    row["selected_mode_count"] = int(len(shell_modes))
    row["triad_count"] = int(len(triads))
    row["carrier_stratum_count"] = int(frame_metrics.get("carrier_stratum_count", 0))
    if len(shell_modes) < 3 or not triads:
        row["status"] = PARTIAL_STATUS
        row["warnings"] = ["no_shell_triads_or_insufficient_modes"]
        return row

    amplitudes = np.asarray([float(mode.amplitude) for mode in shell_modes], dtype=np.float64)
    base_probability = _normalize_profile(amplitudes * amplitudes, zero_eps)
    shell_radii = np.asarray([float(mode.shell_radius) for mode in shell_modes], dtype=np.float64)
    levels = _shell_levels(shell_radii)

    candidates: list[dict[str, Any]] = []
    for seed in seeds:
        for profile_id, probability in _candidate_profiles(base_probability, levels, sample_count, mix_count, seed, zero_eps):
            evaluated = _evaluate_profile(triads, probability, levels, zero_eps, high_shell_cutoff)
            branch = _branch(evaluated, c0=c0, r0=r0, high_shell_eta=high_shell_eta, d0=d0)
            lmin = evaluated.get("lambda_min_kn_a")
            product = (
                float(lmin) * (float(evaluated["n_eff"]) ** 2.5)
                if isinstance(lmin, (int, float)) and math.isfinite(float(lmin))
                else None
            )
            radial_high = (
                float(evaluated["radial_effective_scale"]) >= float(r0)
                or float(evaluated["high_shell_mass_fraction"]) >= float(high_shell_eta)
            )
            old_angular_feasible = (
                float(evaluated["n_eff"]) >= float(n0)
                and float(evaluated["dissipation_proxy"]) <= float(d0)
                and evaluated["status"] == OK_STATUS
            )
            candidates.append(
                {
                    "profile_id": profile_id,
                    "seed": int(seed),
                    "status": evaluated["status"],
                    "lambda_min_kn_a": lmin,
                    "lambda_max_kn_a": evaluated.get("lambda_max_kn_a"),
                    "energy": evaluated["energy"],
                    "n_eff": evaluated["n_eff"],
                    "angular_mode_count": int(evaluated["angular_mode_count"]),
                    "angular_entropy": evaluated["angular_entropy"],
                    "radial_shell_min": evaluated["radial_shell_min"],
                    "radial_shell_max": evaluated["radial_shell_max"],
                    "radial_shell_barycenter": evaluated["radial_shell_barycenter"],
                    "radial_shell_variance": evaluated["radial_shell_variance"],
                    "radial_effective_scale": evaluated["radial_effective_scale"],
                    "high_shell_mass_fraction": evaluated["high_shell_mass_fraction"],
                    "high_shell_mass_by_cutoff": evaluated["high_shell_mass_by_cutoff"],
                    "dissipation_proxy": evaluated["dissipation_proxy"],
                    "bkm_proxy": evaluated["bkm_proxy"],
                    "product_separation_lambda_min_times_n_eff_5_over_2": product,
                    "branch": branch,
                    "feasible_constraint": bool(
                        radial_high
                        and float(evaluated["dissipation_proxy"]) <= float(d0)
                        and evaluated["status"] == OK_STATUS
                    ),
                    "old_angular_feasible_constraint": bool(old_angular_feasible),
                    "angular_multiplicity_artifact": bool(
                        old_angular_feasible
                        and not radial_high
                        and isinstance(lmin, (int, float))
                        and math.isfinite(float(lmin))
                        and float(lmin) < float(c0)
                    ),
                    "triple_danger": branch == "unresolved-danger",
                    "l_abs_positive_rank": evaluated.get("l_abs_positive_rank"),
                    "worst_eigenvector_shell": evaluated.get("worst_eigenvector_shell"),
                    "worst_eigenvector_shell_mass_fraction": evaluated.get("worst_eigenvector_shell_mass_fraction"),
                }
            )

    ok_candidates = [candidate for candidate in candidates if candidate["status"] == OK_STATUS]
    feasible = [candidate for candidate in ok_candidates if candidate["feasible_constraint"]]
    triple_danger = [candidate for candidate in ok_candidates if candidate["triple_danger"]]
    best_feasible = min(feasible, key=lambda item: float(item["lambda_min_kn_a"])) if feasible else None
    best_any = min(ok_candidates, key=lambda item: float(item["lambda_min_kn_a"])) if ok_candidates else None
    worst_product = min(
        (candidate for candidate in ok_candidates if candidate["product_separation_lambda_min_times_n_eff_5_over_2"] is not None),
        key=lambda item: float(item["product_separation_lambda_min_times_n_eff_5_over_2"]),
        default=None,
    )

    row.update(
        {
            "status": OK_STATUS if ok_candidates else PARTIAL_STATUS,
            "profile_count": int(len(candidates)),
            "ok_profile_count": int(len(ok_candidates)),
            "feasible_profile_count": int(len(feasible)),
            "triple_danger_count": int(len(triple_danger)),
            "no_triple_danger_sampled": len(triple_danger) == 0,
            "angular_multiplicity_artifact_count": int(
                sum(1 for candidate in ok_candidates if candidate.get("angular_multiplicity_artifact") is True)
            ),
            "best_feasible_profile": best_feasible,
            "best_any_profile": best_any,
            "worst_product_separation_profile": worst_product,
            "profile_samples": sorted(
                ok_candidates,
                key=lambda item: (
                    0 if item["triple_danger"] else 1,
                    float(item["lambda_min_kn_a"]),
                ),
            )[: min(max(0, int(profile_sample_limit)), len(ok_candidates))],
        }
    )
    return row


def _aggregate(rows: list[dict[str, Any]]) -> dict[str, Any]:
    ok_rows = [row for row in rows if row.get("status") == OK_STATUS]
    best_rows = [row.get("best_feasible_profile") for row in ok_rows if isinstance(row.get("best_feasible_profile"), dict)]
    danger_count = sum(int(row.get("triple_danger_count", 0)) for row in ok_rows)
    if best_rows:
        best_global = min(best_rows, key=lambda item: float(item["lambda_min_kn_a"]))
    else:
        best_global = None
    return {
        "processed_rows": int(len(rows)),
        "ok_rows": int(len(ok_rows)),
        "partial_rows": int(sum(1 for row in rows if row.get("status") == PARTIAL_STATUS)),
        "error_rows": int(sum(1 for row in rows if row.get("status") == ERROR_STATUS)),
        "sampled_profile_count": int(sum(int(row.get("profile_count", 0)) for row in rows)),
        "feasible_profile_count": int(sum(int(row.get("feasible_profile_count", 0)) for row in rows)),
        "triple_danger_count": int(danger_count),
        "no_triple_danger_sampled": danger_count == 0,
        "angular_multiplicity_artifact_count": int(
            sum(int(row.get("angular_multiplicity_artifact_count", 0)) for row in ok_rows)
        ),
        "best_global_feasible_profile": best_global,
        "constrained_adversarial_fork_status": "fail-closed",
        "bandwidth_variable_status": "corrected_to_radial_diagnostic",
        "old_angular_n_eff_status": "diagnostic_only_not_radial_bandwidth",
        "candidate_only": True,
        "fail_closed": True,
        "theorem_promoted": False,
        "full_ns_promoted": False,
        "clay_promoted": False,
        "wall1a_status": "unproved",
        "wall1b_status": "unproved",
        "determinant_growth_status": "unproved",
        "rarity_status": "unproved",
        "residence_time_exclusion_status": "unproved",
    }


def main() -> int:
    args = _parse_args()
    shells = _validate_shells(args.shells if args.shells is not None else list(DEFAULT_SHELLS))
    seeds = [int(seed) for seed in (args.seeds if args.seeds is not None else list(DEFAULT_SEEDS))]
    warnings: list[str] = []
    bundle = _load_raw_bundle(Path(args.raw_archive), warnings)
    snapshots = _frame_indices(bundle.frame_count, frame=args.frame, frame_limit=args.frame_limit)
    rows: list[dict[str, Any]] = []
    for slot, snapshot in enumerate(snapshots):
        for shell_n in shells:
            rows.append(
                _row(
                    slot=slot,
                    snapshot=snapshot,
                    bundle=bundle,
                    shell_n=shell_n,
                    top_k=int(args.top_k),
                    pool_multiplier=int(args.pool_multiplier),
                    zero_eps=float(args.zero_eps),
                    sample_count=int(args.sample_count),
                    mix_count=int(args.mix_count),
                    seeds=seeds,
                    c0=float(args.c0),
                    n0=float(args.n0),
                    d0=float(args.d0),
                    r0=float(args.r0),
                    high_shell_cutoff=float(args.high_shell_cutoff),
                    high_shell_eta=float(args.high_shell_eta),
                    profile_sample_limit=int(args.profile_sample_limit),
                )
            )

    payload = {
        "script_name": SCRIPT_NAME,
        "contract": CONTRACT,
        "route_decision": ROUTE_DECISION,
        "schema_version": SCHEMA_VERSION,
        "authority": AUTHORITY,
        "control_card": CONTROL_CARD,
        "parameters": {
            "raw_archive": str(args.raw_archive),
            "output_json": str(args.output_json),
            "frame": args.frame,
            "frame_limit": args.frame_limit,
            "top_k": int(args.top_k),
            "pool_multiplier": int(args.pool_multiplier),
            "zero_eps": float(args.zero_eps),
            "sample_count": int(args.sample_count),
            "mix_count": int(args.mix_count),
            "profile_sample_limit": int(args.profile_sample_limit),
            "seeds": seeds,
            "shells": [int(shell) for shell in shells],
            "c0": float(args.c0),
            "n0": float(args.n0),
            "d0": float(args.d0),
            "r0": float(args.r0),
            "high_shell_cutoff": float(args.high_shell_cutoff),
            "high_shell_eta": float(args.high_shell_eta),
        },
        "status": OK_STATUS if not any(row.get("status") == ERROR_STATUS for row in rows) else PARTIAL_STATUS,
        "ok": not any(row.get("status") == ERROR_STATUS for row in rows),
        "warnings": warnings,
        "rows": rows,
        "aggregate": _aggregate(rows),
    }
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(_json_text(payload, args.pretty) + "\n", encoding="utf-8")
    print(_json_text(payload, args.pretty))
    return 0 if payload["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
