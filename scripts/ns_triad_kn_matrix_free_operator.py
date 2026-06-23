#!/usr/bin/env python3
"""Matrix-free K_N(A) Laplacian operators for NS triad scans.

The current Dashi triad K_N(A) convention is the weighted pair-Laplacian route
used by ``ns_triad_constrained_adversarial_fork_optimizer.py``:

    L_abs(A) = L_pos(A) + L_neg(A)
    K_N(A) = L_abs(A)^(-1/2) L_neg(A) L_abs(A)^(-1/2)

This module keeps that convention but exposes matvecs instead of requiring
callers to materialize K_N(A).  The dense adapters are intentionally small-shell
parity tools and not a production dense eigensolver lane.
"""

from __future__ import annotations

from dataclasses import dataclass
import math
from typing import Any

import numpy as np

OK_STATUS = "ok"
PARTIAL_STATUS = "partial"


@dataclass(frozen=True)
class MatrixFreeKNProfile:
    """Weighted triad-pair incidence data for L_abs and L_neg matvecs."""

    mode_count: int
    edge_left: np.ndarray
    edge_right: np.ndarray
    weights_abs: np.ndarray
    weights_neg: np.ndarray
    shell_levels: np.ndarray | None = None
    profile_id: str = "unnamed"


def _as_vector(x: np.ndarray, mode_count: int) -> np.ndarray:
    vec = np.asarray(x, dtype=np.float64)
    if vec.ndim != 1 or int(vec.shape[0]) != int(mode_count):
        raise ValueError(f"x must be a length-{mode_count} vector")
    return vec


def _edge_laplacian_matvec(x: np.ndarray, left: np.ndarray, right: np.ndarray, weights: np.ndarray) -> np.ndarray:
    out = np.zeros_like(x, dtype=np.float64)
    if len(weights) == 0:
        return out
    diff = x[left] - x[right]
    contrib = weights * diff
    np.add.at(out, left, contrib)
    np.add.at(out, right, -contrib)
    return out


def matvec_abs(x: np.ndarray, profile: MatrixFreeKNProfile) -> np.ndarray:
    """Return ``L_abs(A) x`` using weighted edge incidence."""

    vec = _as_vector(x, profile.mode_count)
    return _edge_laplacian_matvec(vec, profile.edge_left, profile.edge_right, profile.weights_abs)


def matvec_neg(x: np.ndarray, profile: MatrixFreeKNProfile) -> np.ndarray:
    """Return ``L_neg(A) x`` using weighted edge incidence."""

    vec = _as_vector(x, profile.mode_count)
    return _edge_laplacian_matvec(vec, profile.edge_left, profile.edge_right, profile.weights_neg)


def rayleigh(x: np.ndarray, profile: MatrixFreeKNProfile, zero_eps: float = 1.0e-12) -> float:
    """Generalized Rayleigh quotient ``x.T L_neg x / x.T L_abs x``."""

    vec = _as_vector(x, profile.mode_count)
    denominator = float(vec @ matvec_abs(vec, profile))
    if not math.isfinite(denominator) or abs(denominator) <= float(zero_eps):
        return float("nan")
    numerator = float(vec @ matvec_neg(vec, profile))
    return float(numerator / denominator)


def build_profile(
    triads: list[Any],
    probability: np.ndarray,
    mode_count: int,
    zero_eps: float,
    shell_levels: np.ndarray | None = None,
    profile_id: str = "unnamed",
) -> MatrixFreeKNProfile:
    """Build weighted edge-incidence arrays matching the existing dense oracle."""

    amplitude = np.sqrt(np.maximum(np.asarray(probability, dtype=np.float64), 0.0))
    left_edges: list[int] = []
    right_edges: list[int] = []
    weights_abs: list[float] = []
    weights_neg: list[float] = []
    for triad in triads:
        left = int(triad.left)
        right = int(triad.right)
        out = int(triad.out)
        raw_weight = float(amplitude[left] * amplitude[right] * amplitude[out])
        if not math.isfinite(raw_weight) or raw_weight <= float(zero_eps):
            continue
        pair_weight = raw_weight / 3.0
        coherence = float(triad.coherence)
        positive_weight = pair_weight * max(coherence, 0.0)
        negative_weight = pair_weight * max(-coherence, 0.0)
        absolute_weight = positive_weight + negative_weight
        if absolute_weight <= float(zero_eps):
            continue
        for a, b in ((left, right), (left, out), (right, out)):
            left_edges.append(a)
            right_edges.append(b)
            weights_abs.append(absolute_weight)
            weights_neg.append(negative_weight)
    return MatrixFreeKNProfile(
        mode_count=int(mode_count),
        edge_left=np.asarray(left_edges, dtype=np.int64),
        edge_right=np.asarray(right_edges, dtype=np.int64),
        weights_abs=np.asarray(weights_abs, dtype=np.float64),
        weights_neg=np.asarray(weights_neg, dtype=np.float64),
        shell_levels=None if shell_levels is None else np.asarray(shell_levels, dtype=np.float64),
        profile_id=str(profile_id),
    )


def dense_laplacians_from_matvec(profile: MatrixFreeKNProfile) -> tuple[np.ndarray, np.ndarray]:
    """Materialize ``L_abs`` and ``L_neg`` by applying the matvecs to basis vectors."""

    n = int(profile.mode_count)
    l_abs = np.zeros((n, n), dtype=np.float64)
    l_neg = np.zeros((n, n), dtype=np.float64)
    for index in range(n):
        basis = np.zeros(n, dtype=np.float64)
        basis[index] = 1.0
        l_abs[:, index] = matvec_abs(basis, profile)
        l_neg[:, index] = matvec_neg(basis, profile)
    return 0.5 * (l_abs + l_abs.T), 0.5 * (l_neg + l_neg.T)


def _positive_subspace(matrix: np.ndarray, tol: float) -> tuple[np.ndarray, np.ndarray]:
    evals, evecs = np.linalg.eigh(0.5 * (matrix + matrix.T))
    mask = np.asarray(evals > float(tol), dtype=bool)
    return np.asarray(evals[mask], dtype=np.float64), np.asarray(evecs[:, mask], dtype=np.float64)


def dense_parity_adapter(profile: MatrixFreeKNProfile, zero_eps: float = 1.0e-12) -> dict[str, Any]:
    """Small-shell dense generalized solve derived from matrix-free matvecs."""

    l_abs, l_neg = dense_laplacians_from_matvec(profile)
    tol = max(float(zero_eps), 1.0e-10)
    evals, basis = _positive_subspace(l_abs, tol=tol)
    if len(evals) == 0:
        return {
            "status": PARTIAL_STATUS,
            "lambda_min": None,
            "lambda_max": None,
            "eigenvalues": [],
            "l_abs_positive_rank": 0,
            "worst_eigenvector": None,
            "worst_eigenvector_shell": None,
            "worst_eigenvector_shell_mass_fraction": None,
            "warnings": ["l_abs_has_no_positive_subspace"],
        }
    scale = np.asarray([1.0 / math.sqrt(float(value)) for value in evals], dtype=np.float64)
    reduced = (basis * scale).T @ l_neg @ (basis * scale)
    reduced = 0.5 * (reduced + reduced.T)
    k_eigs, k_vecs = np.linalg.eigh(reduced)
    worst_index = int(np.argmin(k_eigs))
    full_vec = np.asarray((basis * scale) @ k_vecs[:, worst_index], dtype=np.float64)
    norm = float(np.linalg.norm(full_vec))
    if norm > float(zero_eps):
        full_vec = full_vec / norm
    shell = None
    shell_mass_fraction = None
    if profile.shell_levels is not None:
        masses = full_vec * full_vec
        total_mass = float(np.sum(masses))
        shell_mass: dict[int, float] = {}
        for shell_value, mass in zip(profile.shell_levels, masses, strict=False):
            shell_key = int(shell_value)
            shell_mass[shell_key] = shell_mass.get(shell_key, 0.0) + float(mass)
        if shell_mass:
            shell, shell_mass = max(shell_mass.items(), key=lambda item: item[1])
            shell_mass_fraction = float(shell_mass / max(total_mass, float(zero_eps)))
    return {
        "status": OK_STATUS,
        "lambda_min": float(np.min(k_eigs)),
        "lambda_max": float(np.max(k_eigs)),
        "eigenvalues": [float(value) for value in k_eigs],
        "l_abs_positive_rank": int(len(evals)),
        "worst_eigenvector": full_vec,
        "worst_eigenvector_shell": shell,
        "worst_eigenvector_shell_mass_fraction": shell_mass_fraction,
        "warnings": [],
    }

