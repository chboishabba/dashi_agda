from __future__ import annotations

import itertools
import math
from pathlib import Path
from typing import Any

import numpy as np


def frequency_grid(n: int) -> tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray]:
    axis = np.fft.fftfreq(n) * n
    kz, ky, kx = np.meshgrid(axis, axis, axis, indexing="ij")
    wave = np.stack((kx, ky, kz), axis=-1)
    norm_sq = np.sum(wave * wave, axis=-1)
    norm = np.sqrt(norm_sq)
    dealias = np.all(np.abs(wave) <= float(n) / 3.0, axis=-1)
    return wave, norm_sq, norm, dealias


def packet_mask(norm: np.ndarray, shell: int, dealias: np.ndarray | None = None) -> np.ndarray:
    mask = (norm >= float(2 ** shell)) & (norm < float(2 ** (shell + 1)))
    return mask if dealias is None else mask & dealias


def spectral_gradient(hat: np.ndarray, wave: np.ndarray) -> np.ndarray:
    if hat.ndim != 4 or hat.shape[-1] != 3:
        raise ValueError("hat must have shape (N,N,N,3)")
    grad = np.empty(hat.shape[:3] + (3, 3), dtype=np.float64)
    for component in range(3):
        for derivative in range(3):
            grad[..., component, derivative] = np.fft.ifftn(
                1j * wave[..., derivative] * hat[..., component], axes=(0, 1, 2)
            ).real
    return grad


def strain_from_gradient(grad: np.ndarray) -> np.ndarray:
    return 0.5 * (grad + np.swapaxes(grad, -1, -2))


def curl_from_gradient(grad: np.ndarray) -> np.ndarray:
    omega = np.empty(grad.shape[:-2] + (3,), dtype=np.float64)
    omega[..., 0] = grad[..., 2, 1] - grad[..., 1, 2]
    omega[..., 1] = grad[..., 0, 2] - grad[..., 2, 0]
    omega[..., 2] = grad[..., 1, 0] - grad[..., 0, 1]
    return omega


def leray_project_hat(vector_hat: np.ndarray, wave: np.ndarray, norm_sq: np.ndarray) -> np.ndarray:
    dot = np.einsum("...i,...i->...", wave, vector_hat)
    correction = np.zeros_like(vector_hat)
    nonzero = norm_sq > 0.0
    correction[nonzero] = wave[nonzero] * (dot[nonzero] / norm_sq[nonzero])[:, None]
    result = vector_hat - correction
    result[~nonzero] = 0.0
    return result


def nonlinear_momentum_components(input_hat: np.ndarray, wave: np.ndarray,
                                  norm_sq: np.ndarray, dealias: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    """Return advective and pressure acceleration hats for a dealiased input."""
    u = np.fft.ifftn(input_hat, axes=(0, 1, 2)).real
    grad = spectral_gradient(input_hat, wave)
    convection = np.einsum("...j,...ij->...i", u, grad)
    convection_hat = np.fft.fftn(convection, axes=(0, 1, 2))
    advective_hat = -convection_hat
    dot = np.einsum("...i,...i->...", wave, convection_hat)
    pressure_hat = np.zeros_like(convection_hat)
    nonzero = norm_sq > 0.0
    pressure_hat[nonzero] = wave[nonzero] * (dot[nonzero] / norm_sq[nonzero])[:, None]
    advective_hat *= dealias[..., None]
    pressure_hat *= dealias[..., None]
    return advective_hat, pressure_hat


def galerkin_packet_rhs_components(raw_hat: np.ndarray, nu: float, target_shell: int) -> dict[str, Any]:
    if raw_hat.ndim != 4 or raw_hat.shape[-1] != 3 or len(set(raw_hat.shape[:3])) != 1:
        raise ValueError(f"expected raw_hat shape (N,N,N,3), got {raw_hat.shape!r}")
    if not math.isfinite(nu) or nu <= 0.0:
        raise ValueError("viscosity must be finite and positive")
    n = int(raw_hat.shape[0])
    wave, norm_sq, norm, dealias = frequency_grid(n)
    retained_hat = np.asarray(raw_hat, dtype=np.complex128) * dealias[..., None]
    retained_hat = leray_project_hat(retained_hat, wave, norm_sq)
    packet = packet_mask(norm, target_shell, dealias)
    packet_hat = retained_hat * packet[..., None]

    full_adv, full_pressure = nonlinear_momentum_components(retained_hat, wave, norm_sq, dealias)
    self_adv, self_pressure = nonlinear_momentum_components(packet_hat, wave, norm_sq, dealias)
    full_adv *= packet[..., None]
    full_pressure *= packet[..., None]
    self_adv *= packet[..., None]
    self_pressure *= packet[..., None]
    components = {
        "self_advective": self_adv,
        "self_pressure": self_pressure,
        "cross_shell_advective": full_adv - self_adv,
        "cross_shell_pressure": full_pressure - self_pressure,
        "viscous": -nu * norm_sq[..., None] * packet_hat,
    }
    total = sum(components.values(), np.zeros_like(packet_hat))
    direct = full_adv + full_pressure - nu * norm_sq[..., None] * packet_hat
    return {
        "cutoff": n,
        "wave": wave,
        "norm_sq": norm_sq,
        "norm": norm,
        "dealias": dealias,
        "packet": packet,
        "retained_hat": retained_hat,
        "packet_hat": packet_hat,
        "components": components,
        "total_rhs_hat": total,
        "rhs_decomposition_max_residual": float(np.max(np.abs(total - direct))),
        "retained_divergence_max_residual": float(np.max(np.abs(np.einsum("...i,...i->...", wave, retained_hat)))),
    }


def _soft_projector_and_derivative(eigenvalues: np.ndarray, eigenvectors: np.ndarray,
                                   strain_dot: np.ndarray, beta: float) -> tuple[np.ndarray, np.ndarray]:
    shifted = eigenvalues - np.max(eigenvalues, axis=-1, keepdims=True)
    exponentials = np.exp(beta * shifted)
    z = np.sum(exponentials, axis=-1)
    weights = exponentials / z[..., None]
    projector = np.einsum("...ia,...a,...ja->...ij", eigenvectors, weights, eigenvectors)
    b = np.einsum("...ia,...ij,...jb->...ab", eigenvectors, strain_dot, eigenvectors)
    li = eigenvalues[..., :, None]
    lj = eigenvalues[..., None, :]
    ei = exponentials[..., :, None]
    ej = exponentials[..., None, :]
    gap = li - lj
    close = np.abs(gap) <= 1.0e-12 * (1.0 + np.maximum(np.abs(li), np.abs(lj)))
    safe_gap = np.where(close, 1.0, gap)
    divided = np.where(close, beta * 0.5 * (ei + ej), (ei - ej) / safe_gap)
    dw = divided * b
    dz = np.trace(dw, axis1=-2, axis2=-1)
    dp_eigen = dw / z[..., None, None]
    for i in range(3):
        dp_eigen[..., i, i] -= exponentials[..., i] * dz / (z * z)
    dprojector = np.einsum("...ia,...ab,...jb->...ij", eigenvectors, dp_eigen, eigenvectors)
    return projector, dprojector


def exact_alignment_budget(raw_hat: np.ndarray, nu: float, target_shell: int,
                           *, soft_beta_dimensionless: float = 8.0,
                           gap_relative_floor: float = 1.0e-4) -> dict[str, Any]:
    rhs = galerkin_packet_rhs_components(raw_hat, nu, target_shell)
    wave = rhs["wave"]
    packet_grad = spectral_gradient(rhs["packet_hat"], wave)
    strain = strain_from_gradient(packet_grad)
    omega = curl_from_gradient(packet_grad)
    omega_sq = np.sum(omega * omega, axis=-1)
    enstrophy = float(np.mean(omega_sq))
    if enstrophy <= 1.0e-30:
        raise ValueError("target packet has zero enstrophy")

    eigenvalues, eigenvectors = np.linalg.eigh(strain)
    eigenvalues = eigenvalues[..., ::-1]
    eigenvectors = eigenvectors[..., :, ::-1]
    projections = np.einsum("...ji,...j->...i", eigenvectors, omega)
    alpha = np.divide(projections * projections, omega_sq[..., None],
                      out=np.zeros_like(projections), where=omega_sq[..., None] > 1.0e-30)
    hard_n = float(np.mean(projections[..., 0] ** 2))
    hard_a = hard_n / enstrophy

    parabolic_rate = nu * float(2 ** (2 * target_shell))
    beta = soft_beta_dimensionless / parabolic_rate
    soft_projector, _ = _soft_projector_and_derivative(
        eigenvalues, eigenvectors, np.zeros_like(strain), beta
    )
    pomega = np.einsum("...ij,...j->...i", soft_projector, omega)
    soft_n = float(np.mean(np.einsum("...i,...i->...", omega, pomega)))
    soft_a = soft_n / enstrophy

    component_rows: dict[str, dict[str, float]] = {}
    total_e_dot = total_n_dot = total_a_dot = 0.0
    pressure_strain_dot = np.zeros_like(strain)
    for name, component_hat in rhs["components"].items():
        grad_dot = spectral_gradient(component_hat, wave)
        strain_dot = strain_from_gradient(grad_dot)
        omega_dot = curl_from_gradient(grad_dot)
        _, projector_dot = _soft_projector_and_derivative(eigenvalues, eigenvectors, strain_dot, beta)
        e_dot = float(2.0 * np.mean(np.einsum("...i,...i->...", omega, omega_dot)))
        n_dot = float(np.mean(
            2.0 * np.einsum("...i,...i->...", omega_dot, pomega)
            + np.einsum("...i,...ij,...j->...", omega, projector_dot, omega)
        ))
        a_dot = (n_dot * enstrophy - soft_n * e_dot) / (enstrophy * enstrophy)
        component_rows[name] = {
            "enstrophy_derivative": e_dot,
            "alignment_numerator_derivative": n_dot,
            "normalized_alignment_derivative": a_dot,
            "parabolic_normalized_alignment_derivative": a_dot / parabolic_rate,
        }
        total_e_dot += e_dot
        total_n_dot += n_dot
        total_a_dot += a_dot
        if "pressure" in name:
            pressure_strain_dot += strain_dot

    total_grad_dot = spectral_gradient(rhs["total_rhs_hat"], wave)
    total_strain_dot = strain_from_gradient(total_grad_dot)
    total_omega_dot = curl_from_gradient(total_grad_dot)
    _, total_projector_dot = _soft_projector_and_derivative(eigenvalues, eigenvectors, total_strain_dot, beta)
    direct_e_dot = float(2.0 * np.mean(np.einsum("...i,...i->...", omega, total_omega_dot)))
    direct_n_dot = float(np.mean(
        2.0 * np.einsum("...i,...i->...", total_omega_dot, pomega)
        + np.einsum("...i,...ij,...j->...", omega, total_projector_dot, omega)
    ))
    direct_a_dot = (direct_n_dot * enstrophy - soft_n * direct_e_dot) / (enstrophy * enstrophy)

    strain_scale = np.sqrt(np.sum(eigenvalues * eigenvalues, axis=-1))
    gap12 = eigenvalues[..., 0] - eigenvalues[..., 1]
    gap13 = eigenvalues[..., 0] - eigenvalues[..., 2]
    gap23 = eigenvalues[..., 1] - eigenvalues[..., 2]
    floor = gap_relative_floor * strain_scale + 1.0e-30
    simple = (gap12 > floor) & (gap13 > floor) & (omega_sq > 1.0e-30)
    top_pair = (gap12 <= floor) & (gap23 > floor) & (omega_sq > 1.0e-30)
    triple = (gap12 <= floor) & (gap23 <= floor) & (omega_sq > 1.0e-30)
    bpressure = np.einsum("...ia,...ij,...jb->...ab", eigenvectors, pressure_strain_dot, eigenvectors)
    hard_pressure_density = np.zeros_like(omega_sq)
    hard_pressure_density[simple] = 2.0 * projections[..., 0][simple] * (
        projections[..., 1][simple] * bpressure[..., 1, 0][simple] / gap12[simple]
        + projections[..., 2][simple] * bpressure[..., 2, 0][simple] / gap13[simple]
    )
    hard_pressure_a_dot = float(np.mean(hard_pressure_density)) / enstrophy
    cluster_pressure_density = np.zeros_like(omega_sq)
    cluster_pressure_density[top_pair] = 2.0 * projections[..., 2][top_pair] * (
        projections[..., 0][top_pair] * bpressure[..., 2, 0][top_pair] / gap13[top_pair]
        + projections[..., 1][top_pair] * bpressure[..., 2, 1][top_pair] / gap23[top_pair]
    )

    self_adv = component_rows["self_advective"]["parabolic_normalized_alignment_derivative"]
    self_pressure = component_rows["self_pressure"]["parabolic_normalized_alignment_derivative"]
    cross_adv = component_rows["cross_shell_advective"]["parabolic_normalized_alignment_derivative"]
    cross_pressure = component_rows["cross_shell_pressure"]["parabolic_normalized_alignment_derivative"]
    viscous = component_rows["viscous"]["parabolic_normalized_alignment_derivative"]
    local_depletion = max(-self_adv, 0.0)
    pressure_remainder = max(self_pressure + cross_pressure, 0.0)
    commutator_remainder = max(cross_adv, 0.0)
    viscous_remainder = max(viscous, 0.0)
    total_positive_remainder = max(self_pressure + cross_pressure + cross_adv + viscous, 0.0)
    active_weight = omega_sq / float(np.sum(omega_sq))

    def weighted_fraction(mask: np.ndarray) -> float:
        return float(np.sum(active_weight[mask]))

    return {
        "cutoff": rhs["cutoff"],
        "target_shell": target_shell,
        "physical_viscosity": nu,
        "parabolic_rate": parabolic_rate,
        "rhs_decomposition_max_residual": rhs["rhs_decomposition_max_residual"],
        "retained_divergence_max_residual": rhs["retained_divergence_max_residual"],
        "packet_enstrophy_E": enstrophy,
        "hard_alignment_numerator_N1": hard_n,
        "hard_alignment_A1": hard_a,
        "soft_projector_beta_dimensionless": soft_beta_dimensionless,
        "soft_projector_beta_physical": beta,
        "soft_alignment_numerator_N": soft_n,
        "soft_alignment_A": soft_a,
        "component_derivatives": component_rows,
        "exact_total_derivatives": {
            "enstrophy_derivative": direct_e_dot,
            "alignment_numerator_derivative": direct_n_dot,
            "normalized_alignment_derivative": direct_a_dot,
            "parabolic_normalized_alignment_derivative": direct_a_dot / parabolic_rate,
            "component_sum_enstrophy_residual": abs(total_e_dot - direct_e_dot),
            "component_sum_numerator_residual": abs(total_n_dot - direct_n_dot),
            "component_sum_alignment_residual": abs(total_a_dot - direct_a_dot),
            "quotient_rule_residual": abs(
                direct_a_dot - (direct_n_dot * enstrophy - soft_n * direct_e_dot) / (enstrophy * enstrophy)
            ),
        },
        "gauge_invariant_pressure": {
            "hard_A1_pressure_derivative_simple_spectrum": hard_pressure_a_dot,
            "hard_A1_pressure_derivative_parabolic_normalized": hard_pressure_a_dot / parabolic_rate,
            "simple_top_eigenvalue_enstrophy_fraction": weighted_fraction(simple),
            "top_pair_degenerate_enstrophy_fraction": weighted_fraction(top_pair),
            "triple_degenerate_enstrophy_fraction": weighted_fraction(triple),
            "top_pair_cluster_pressure_numerator_derivative": float(np.mean(cluster_pressure_density)),
            "gap_relative_floor": gap_relative_floor,
            "raw_signed_mix_positive_part_used": False,
        },
        "candidate_absorption": {
            "local_geometric_depletion": local_depletion,
            "pressure_positive_remainder": pressure_remainder,
            "commutator_positive_remainder": commutator_remainder,
            "viscous_positive_remainder": viscous_remainder,
            "total_positive_remainder": total_positive_remainder,
            "theta_emp_pointwise": total_positive_remainder / local_depletion if local_depletion > 0.0 else None,
        },
        "middle_eigenvalue": {
            "lambda2_positive_enstrophy_fraction": weighted_fraction(eigenvalues[..., 1] > 0.0),
            "alpha2_weighted_mean": float(np.sum(active_weight * alpha[..., 1])),
        },
    }


def weighted_quantile(values: np.ndarray, weights: np.ndarray,
                      quantiles: tuple[float, ...]) -> list[float]:
    values = np.asarray(values, dtype=float).ravel()
    weights = np.asarray(weights, dtype=float).ravel()
    valid = np.isfinite(values) & np.isfinite(weights) & (weights > 0.0)
    if not np.any(valid):
        return [0.0 for _ in quantiles]
    values = values[valid]
    weights = weights[valid]
    order = np.argsort(values)
    values = values[order]
    weights = weights[order]
    cumulative = np.cumsum(weights)
    cumulative /= cumulative[-1]
    return [float(np.interp(q, cumulative, values)) for q in quantiles]


def periodic_box_sum(values: np.ndarray, radius: int) -> np.ndarray:
    result = values.astype(np.float64, copy=True)
    for axis in range(3):
        base = result
        result = np.zeros_like(base)
        for shift in range(-radius, radius + 1):
            result += np.roll(base, shift, axis=axis)
    return result


def multiscale_direction_statistics(xi: np.ndarray, weights: np.ndarray,
                                    radii: tuple[int, ...]) -> dict[str, Any]:
    n = int(weights.shape[0])
    rows: list[dict[str, Any]] = []
    for requested_radius in radii:
        radius = min(requested_radius, max((n - 1) // 2, 1))
        denominator = periodic_box_sum(weights, radius)
        means = np.zeros_like(xi)
        moment = np.zeros(weights.shape + (3, 3), dtype=float)
        for i in range(3):
            numerator = periodic_box_sum(weights * xi[..., i], radius)
            means[..., i] = np.divide(numerator, denominator,
                                      out=np.zeros_like(numerator), where=denominator > 1e-30)
            for j in range(3):
                tensor_num = periodic_box_sum(weights * xi[..., i] * xi[..., j], radius)
                moment[..., i, j] = np.divide(tensor_num, denominator,
                                               out=np.zeros_like(tensor_num), where=denominator > 1e-30)
        vector_osc = np.sqrt(np.maximum(1.0 - np.sum(means * means, axis=-1), 0.0))
        lmax = np.linalg.eigvalsh(moment)[..., -1]
        projective_osc = np.sqrt(np.maximum(1.0 - lmax, 0.0))
        quantiles = (0.5, 0.9, 0.99)
        vector_q = weighted_quantile(vector_osc, weights, quantiles)
        projective_q = weighted_quantile(projective_osc, weights, quantiles)
        window_side = 2 * radius + 1
        relative_scale = min(float(window_side) / float(n), 1.0 - 1.0e-15)
        log_weight = abs(math.log(relative_scale))
        rows.append({
            "requested_grid_radius": requested_radius,
            "grid_radius": radius,
            "window_side": window_side,
            "relative_scale": relative_scale,
            "log_weight": log_weight,
            "vector_oscillation": {
                "weighted_median": vector_q[0],
                "weighted_p90": vector_q[1],
                "weighted_p99": vector_q[2],
                "maximum": float(np.max(vector_osc)),
            },
            "projective_oscillation": {
                "weighted_median": projective_q[0],
                "weighted_p90": projective_q[1],
                "weighted_p99": projective_q[2],
                "maximum": float(np.max(projective_osc)),
            },
            "log_weighted_projective_p99": log_weight * projective_q[2],
            "log_weighted_projective_maximum": log_weight * float(np.max(projective_osc)),
            "radius_clamped": radius != requested_radius,
        })
    return {
        "scale_rows": rows,
        "projective_log_bmo_p99_sup": max(float(row["log_weighted_projective_p99"]) for row in rows),
        "projective_log_bmo_max_sup": max(float(row["log_weighted_projective_maximum"]) for row in rows),
    }


def fit_nonnegative_dominating_coefficients(x: np.ndarray, y: np.ndarray,
                                            names: tuple[str, ...], tol: float = 1e-10) -> dict[str, Any]:
    x = np.asarray(x, dtype=float)
    y = np.asarray(y, dtype=float)
    if x.ndim != 2 or x.shape[1] != len(names) or y.shape != (x.shape[0],):
        raise ValueError("coefficient fit shapes are inconsistent")
    if np.any(x < -tol) or np.any(y < -tol):
        raise ValueError("dominating fit requires nonnegative design and target")
    m = x.shape[1]
    if x.shape[0] == 0 or np.all(y <= tol):
        coeff = np.zeros(m)
    else:
        constraints: list[tuple[np.ndarray, float]] = [(x[i], y[i]) for i in range(x.shape[0])]
        constraints.extend((np.eye(m)[j], 0.0) for j in range(m))
        best: np.ndarray | None = None
        best_key: tuple[float, float] | None = None
        for combo in itertools.combinations(range(len(constraints)), m):
            a = np.vstack([constraints[i][0] for i in combo])
            b = np.asarray([constraints[i][1] for i in combo])
            try:
                candidate = np.linalg.solve(a, b)
            except np.linalg.LinAlgError:
                continue
            if np.any(candidate < -tol) or np.any(x @ candidate < y - tol):
                continue
            candidate = np.maximum(candidate, 0.0)
            key = (float(np.sum(candidate)), float(np.max(candidate)))
            if best_key is None or key < best_key:
                best = candidate
                best_key = key
        if best is None:
            candidate = np.zeros(m)
            for i in range(x.shape[0]):
                positive = np.flatnonzero(x[i] > tol)
                if positive.size == 0 and y[i] > tol:
                    return {"feasible": False, "reason": "positive target with zero feature row"}
                if positive.size:
                    j = int(positive[np.argmax(x[i, positive])])
                    candidate[j] = max(candidate[j], y[i] / x[i, j])
            for _ in range(10 * max(1, x.shape[0])):
                deficits = y - x @ candidate
                i = int(np.argmax(deficits))
                if deficits[i] <= tol:
                    break
                j = int(np.argmax(x[i]))
                if x[i, j] <= tol:
                    return {"feasible": False, "reason": "unrepairable zero feature row"}
                candidate[j] += deficits[i] / x[i, j]
            best = candidate
        coeff = best
    margins = x @ coeff - y
    return {
        "feasible": bool(np.all(margins >= -tol)),
        "coefficients": {name: float(value) for name, value in zip(names, coeff)},
        "coefficient_l1": float(np.sum(coeff)),
        "coefficient_linf": float(np.max(coeff)) if coeff.size else 0.0,
        "minimum_pointwise_margin": float(np.min(margins)) if margins.size else None,
        "maximum_pointwise_slack": float(np.max(margins)) if margins.size else None,
    }


def load_raw_state(path: Path) -> tuple[np.ndarray, float, float | None]:
    with np.load(path, allow_pickle=False) as data:
        raw = np.asarray(data["raw_hat"], dtype=np.complex128)
        nu = float(data["nu"]) if "nu" in data else 1.0e-3
        time = float(data["time"]) if "time" in data else None
    return raw, nu, time
