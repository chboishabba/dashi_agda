#!/usr/bin/env python3
"""Deterministic finite periodic Galerkin engine for NS falsification tests.

This module implements the literal velocity formulation

  d_t u(k) + nu |k|^2 u(k)
    = -i P_k sum_{p+q=k} (u(p) dot q) u(q),

on the max-coordinate cube, with reality and divergence-free projection.
It is used only for finite numerical diagnostics; it has no theorem authority.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Any

import numpy as np

Mode = tuple[int, int, int]


def canonical_positive(k: Mode) -> bool:
    for x in k:
        if x != 0:
            return x > 0
    return False


def hat_weight(shell: int, k: Mode) -> float:
    if shell < 1:
        raise ValueError("shell must be >= 1")
    r = max(abs(x) for x in k)
    lo, mid, hi = 2 ** (shell - 1), 2**shell, 2 ** (shell + 1)
    if r < lo or r > hi:
        return 0.0
    if r <= mid:
        return (r - lo) / (mid - lo)
    return (hi - r) / (hi - mid)


def fmt(x: float) -> str:
    return f"{float(x):.10e}"


@dataclass(frozen=True)
class GalerkinGeometry:
    cutoff: int
    modes: tuple[Mode, ...]
    index: dict[Mode, int]
    kvec: np.ndarray
    ksq: np.ndarray
    projectors: np.ndarray
    neg_index: np.ndarray
    triad_p: tuple[np.ndarray, ...]
    triad_q: tuple[np.ndarray, ...]
    triad_qvec: tuple[np.ndarray, ...]
    shell_weights: dict[int, np.ndarray]


def make_geometry(cutoff: int, max_shell: int | None = None) -> GalerkinGeometry:
    modes = tuple(
        (x, y, z)
        for x in range(-cutoff, cutoff + 1)
        for y in range(-cutoff, cutoff + 1)
        for z in range(-cutoff, cutoff + 1)
        if (x, y, z) != (0, 0, 0)
    )
    index = {k: i for i, k in enumerate(modes)}
    kvec = np.asarray(modes, dtype=np.float64)
    ksq = np.einsum("ij,ij->i", kvec, kvec)
    eye = np.eye(3, dtype=np.float64)
    projectors = np.asarray([eye - np.outer(k, k) / s for k, s in zip(kvec, ksq)])
    neg_index = np.asarray([index[(-k[0], -k[1], -k[2])] for k in modes], dtype=np.int64)

    triad_p: list[np.ndarray] = []
    triad_q: list[np.ndarray] = []
    triad_qvec: list[np.ndarray] = []
    for k in modes:
        ps: list[int] = []
        qs: list[int] = []
        qvs: list[Mode] = []
        for p, pi in index.items():
            q = (k[0] - p[0], k[1] - p[1], k[2] - p[2])
            qi = index.get(q)
            if qi is not None:
                ps.append(pi)
                qs.append(qi)
                qvs.append(q)
        triad_p.append(np.asarray(ps, dtype=np.int64))
        triad_q.append(np.asarray(qs, dtype=np.int64))
        triad_qvec.append(np.asarray(qvs, dtype=np.float64).reshape((-1, 3)))

    if max_shell is None:
        max_shell = max(1, cutoff.bit_length())
    shell_weights = {
        shell: np.asarray([hat_weight(shell, k) for k in modes], dtype=np.float64)
        for shell in range(1, max_shell + 1)
    }
    return GalerkinGeometry(
        cutoff=cutoff,
        modes=modes,
        index=index,
        kvec=kvec,
        ksq=ksq,
        projectors=projectors,
        neg_index=neg_index,
        triad_p=tuple(triad_p),
        triad_q=tuple(triad_q),
        triad_qvec=tuple(triad_qvec),
        shell_weights=shell_weights,
    )


def project_state(g: GalerkinGeometry, u: np.ndarray) -> np.ndarray:
    return np.einsum("nij,nj->ni", g.projectors, u)


def enforce_reality(g: GalerkinGeometry, u: np.ndarray) -> np.ndarray:
    out = np.array(u, dtype=np.complex128, copy=True)
    done: set[int] = set()
    for i, k in enumerate(g.modes):
        if i in done:
            continue
        j = int(g.neg_index[i])
        value = 0.5 * (out[i] + np.conjugate(out[j]))
        out[i] = value
        out[j] = np.conjugate(value)
        done.add(i)
        done.add(j)
    return out


def normalize_state(g: GalerkinGeometry, u: np.ndarray, energy: float = 1.0) -> np.ndarray:
    u = enforce_reality(g, project_state(g, u))
    current = total_energy(u)
    if current == 0:
        return u
    return u * np.sqrt(energy / current)


def random_state(g: GalerkinGeometry, seed: int, energy: float = 1.0) -> np.ndarray:
    rng = np.random.default_rng(seed)
    u = np.zeros((len(g.modes), 3), dtype=np.complex128)
    for i, k in enumerate(g.modes):
        if canonical_positive(k):
            raw = rng.normal(size=3) + 1j * rng.normal(size=3)
            value = g.projectors[i] @ raw
            j = int(g.neg_index[i])
            u[i] = value
            u[j] = np.conjugate(value)
    return normalize_state(g, u, energy)


def rhs(g: GalerkinGeometry, u: np.ndarray, viscosity: float = 1.0) -> np.ndarray:
    du = -viscosity * g.ksq[:, None] * u
    for ki in range(len(g.modes)):
        ps = g.triad_p[ki]
        if ps.size == 0:
            continue
        qs = g.triad_q[ki]
        qvec = g.triad_qvec[ki]
        coefficients = np.einsum("ij,ij->i", u[ps], qvec)
        nonlinear = np.sum(coefficients[:, None] * u[qs], axis=0)
        du[ki] += -1j * (g.projectors[ki] @ nonlinear)
    return enforce_reality(g, project_state(g, du))


def rk4_step(g: GalerkinGeometry, u: np.ndarray, dt: float, viscosity: float = 1.0) -> np.ndarray:
    k1 = rhs(g, u, viscosity)
    k2 = rhs(g, u + 0.5 * dt * k1, viscosity)
    k3 = rhs(g, u + 0.5 * dt * k2, viscosity)
    k4 = rhs(g, u + dt * k3, viscosity)
    return enforce_reality(g, project_state(g, u + dt * (k1 + 2 * k2 + 2 * k3 + k4) / 6.0))


def total_energy(u: np.ndarray) -> float:
    return 0.5 * float(np.sum(np.abs(u) ** 2))


def total_energy_derivative(u: np.ndarray, du: np.ndarray) -> float:
    return float(np.real(np.sum(np.conjugate(u) * du)))


def shell_energies(g: GalerkinGeometry, u: np.ndarray) -> dict[int, float]:
    mode_energy = 0.5 * np.sum(np.abs(u) ** 2, axis=1)
    return {j: float(np.sum((w**2) * mode_energy)) for j, w in g.shell_weights.items()}


def shell_energy_derivatives(g: GalerkinGeometry, u: np.ndarray, du: np.ndarray) -> dict[int, float]:
    mode_derivative = np.real(np.sum(np.conjugate(u) * du, axis=1))
    return {j: float(np.sum((w**2) * mode_derivative)) for j, w in g.shell_weights.items()}


def packet_metrics(g: GalerkinGeometry, u: np.ndarray, K: int, du: np.ndarray | None = None) -> dict[str, float]:
    energies = shell_energies(g, u)
    packet = sum(energies.get(j, 0.0) for j in (K - 1, K, K + 1))
    center = energies.get(K, 0.0)
    total = total_energy(u)
    gamma = center / packet if packet > 0 else 0.0
    off = (total - packet) / total if total > 0 else 0.0
    out = {"total": total, "packet": packet, "center": center, "gamma": gamma, "off": off}
    if du is not None:
        derivatives = shell_energy_derivatives(g, u, du)
        packet_d = sum(derivatives.get(j, 0.0) for j in (K - 1, K, K + 1))
        center_d = derivatives.get(K, 0.0)
        total_d = total_energy_derivative(u, du)
        gamma_d = (center_d * packet - center * packet_d) / (packet * packet) if packet > 0 else 0.0
        off_numerator = total - packet
        off_numerator_d = total_d - packet_d
        off_d = (off_numerator_d * total - off_numerator * total_d) / (total * total) if total > 0 else 0.0
        out.update({"total_derivative": total_d, "packet_derivative": packet_d, "center_derivative": center_d, "gamma_derivative": gamma_d, "off_derivative": off_d})
    return out


def h1_squared(g: GalerkinGeometry, u: np.ndarray) -> float:
    return float(np.sum((1.0 + g.ksq)[:, None] * np.abs(u) ** 2))


def h1_squared_derivative(g: GalerkinGeometry, u: np.ndarray, du: np.ndarray) -> float:
    return 2.0 * float(np.real(np.sum((1.0 + g.ksq)[:, None] * np.conjugate(u) * du)))


def weighted_five_halves(g: GalerkinGeometry, u: np.ndarray) -> float:
    energies = shell_energies(g, u)
    return sum((2.0 ** (2.5 * j)) * np.sqrt(max(0.0, 2.0 * e)) for j, e in energies.items())


def vorticity_fourier_l1(g: GalerkinGeometry, u: np.ndarray) -> float:
    curls = np.cross(g.kvec, u)
    return float(np.sum(np.sqrt(np.sum(np.abs(curls) ** 2, axis=1))))


def chart_shell(g: GalerkinGeometry, u: np.ndarray) -> int | None:
    energies = shell_energies(g, u)
    if not energies or max(energies.values(), default=0.0) <= 0:
        return None
    return max(sorted(energies), key=lambda j: energies[j])


def state_summary(g: GalerkinGeometry, u: np.ndarray, K: int, du: np.ndarray | None = None) -> dict[str, Any]:
    metrics = packet_metrics(g, u, K, du)
    return {
        **{key: fmt(value) for key, value in metrics.items()},
        "h1_squared": fmt(h1_squared(g, u)),
        "h1_squared_derivative": fmt(h1_squared_derivative(g, u, du)) if du is not None else None,
        "weighted_five_halves": fmt(weighted_five_halves(g, u)),
        "vorticity_fourier_l1": fmt(vorticity_fourier_l1(g, u)),
        "selected_chart": chart_shell(g, u),
    }
