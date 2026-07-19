"""Finite SU(2) one-step RG laboratory.

This module deliberately computes finite-lattice objects only. It never promotes
volume-uniform, scale-uniform, or continuum claims. Fields are represented in
su(2) ~= R^3 and group elements by unit quaternions.
"""
from __future__ import annotations

from dataclasses import dataclass
from itertools import combinations
from pathlib import Path
from typing import Iterable, Iterator, Sequence
import json
import math

import numpy as np

Array = np.ndarray


def qmul(a: Array, b: Array) -> Array:
    """Hamilton product, broadcasting over leading dimensions."""
    a = np.asarray(a, dtype=float)
    b = np.asarray(b, dtype=float)
    a0, av = a[..., :1], a[..., 1:]
    b0, bv = b[..., :1], b[..., 1:]
    scalar = a0 * b0 - np.sum(av * bv, axis=-1, keepdims=True)
    vector = a0 * bv + b0 * av + np.cross(av, bv)
    return np.concatenate((scalar, vector), axis=-1)


def qconj(q: Array) -> Array:
    q = np.asarray(q, dtype=float).copy()
    q[..., 1:] *= -1.0
    return q


def qnormalize(q: Array, *, atol: float = 1e-15) -> Array:
    q = np.asarray(q, dtype=float)
    norm = np.linalg.norm(q, axis=-1, keepdims=True)
    if np.any(norm <= atol):
        raise ValueError("cannot normalize a zero quaternion")
    return q / norm


def su2_exp(x: Array) -> Array:
    """Exponential of an imaginary quaternion x in R^3."""
    x = np.asarray(x, dtype=float)
    theta = np.linalg.norm(x, axis=-1, keepdims=True)
    sinc = np.ones_like(theta)
    nz = theta > 1e-12
    sinc[nz] = np.sin(theta[nz]) / theta[nz]
    return np.concatenate((np.cos(theta), sinc * x), axis=-1)


def su2_log(q: Array) -> Array:
    q = qnormalize(q)
    scalar = np.clip(q[..., :1], -1.0, 1.0)
    vector = q[..., 1:]
    theta = np.arctan2(np.linalg.norm(vector, axis=-1, keepdims=True), scalar)
    scale = np.ones_like(theta)
    nv = np.linalg.norm(vector, axis=-1, keepdims=True)
    nz = nv > 1e-12
    scale[nz] = theta[nz] / nv[nz]
    return scale * vector


def adjoint(q: Array, x: Array) -> Array:
    """Quaternion conjugation q (0,x) q* returned as R^3."""
    q = qnormalize(q)
    x = np.asarray(x, dtype=float)
    pure = np.concatenate((np.zeros(x.shape[:-1] + (1,)), x), axis=-1)
    return qmul(qmul(q, pure), qconj(q))[..., 1:]


def adjoint_matrix(q: Array) -> Array:
    basis = np.eye(3)
    return np.stack([adjoint(q, e) for e in basis], axis=1)


@dataclass(frozen=True)
class PeriodicLattice:
    L: int
    dim: int = 4

    def __post_init__(self) -> None:
        if self.L < 1:
            raise ValueError("L must be positive")
        if self.dim < 2:
            raise ValueError("dim must be at least 2")

    @property
    def shape(self) -> tuple[int, ...]:
        return (self.L,) * self.dim

    @property
    def n_sites(self) -> int:
        return self.L ** self.dim

    @property
    def n_bonds(self) -> int:
        return self.dim * self.n_sites

    @property
    def n_plaquettes(self) -> int:
        return math.comb(self.dim, 2) * self.n_sites

    def sites(self) -> Iterator[tuple[int, ...]]:
        yield from np.ndindex(self.shape)

    def shift(self, x: Sequence[int], mu: int, amount: int = 1) -> tuple[int, ...]:
        y = list(x)
        y[mu] = (y[mu] + amount) % self.L
        return tuple(y)

    def site_index(self, x: Sequence[int]) -> int:
        return int(np.ravel_multi_index(tuple(x), self.shape))

    def bond_index(self, x: Sequence[int], mu: int) -> int:
        return self.dim * self.site_index(x) + mu

    def plaquette_index(self, x: Sequence[int], mu: int, nu: int) -> int:
        if not mu < nu:
            raise ValueError("plaquette directions require mu < nu")
        pair = list(combinations(range(self.dim), 2)).index((mu, nu))
        return math.comb(self.dim, 2) * self.site_index(x) + pair


def identity_links(lat: PeriodicLattice) -> Array:
    links = np.zeros(lat.shape + (lat.dim, 4), dtype=float)
    links[..., 0] = 1.0
    return links


def lie_field_to_links(field: Array) -> Array:
    field = np.asarray(field, dtype=float)
    if field.shape[-1] != 3:
        raise ValueError("last field axis must have length 3")
    return su2_exp(field)


def plaquette_holonomy(lat: PeriodicLattice, links: Array, x: Sequence[int], mu: int, nu: int) -> Array:
    x = tuple(x)
    x_mu = lat.shift(x, mu)
    x_nu = lat.shift(x, nu)
    return qmul(
        qmul(links[x + (mu,)], links[x_mu + (nu,)]),
        qmul(qconj(links[x_nu + (mu,)]), qconj(links[x + (nu,)])),
    )


def wilson_action(lat: PeriodicLattice, links: Array, beta: float = 1.0) -> float:
    total = 0.0
    for x in lat.sites():
        for mu, nu in combinations(range(lat.dim), 2):
            total += 1.0 - float(plaquette_holonomy(lat, links, x, mu, nu)[0])
    return beta * total


def coboundary_0(lat: PeriodicLattice, background: Array | None = None) -> Array:
    """Covariant site-to-bond difference, with 3 color components."""
    rows = 3 * lat.n_bonds
    cols = 3 * lat.n_sites
    D = np.zeros((rows, cols), dtype=float)
    if background is None:
        background = identity_links(lat)
    for x in lat.sites():
        sx = lat.site_index(x)
        for mu in range(lat.dim):
            y = lat.shift(x, mu)
            sy = lat.site_index(y)
            b = lat.bond_index(x, mu)
            R = adjoint_matrix(background[x + (mu,)])
            D[3*b:3*b+3, 3*sy:3*sy+3] = R
            D[3*b:3*b+3, 3*sx:3*sx+3] -= np.eye(3)
    return D


def coboundary_1(lat: PeriodicLattice, background: Array | None = None) -> Array:
    """Linearized covariant curl from bonds to oriented plaquettes."""
    rows = 3 * lat.n_plaquettes
    cols = 3 * lat.n_bonds
    d1 = np.zeros((rows, cols), dtype=float)
    if background is None:
        background = identity_links(lat)
    for x in lat.sites():
        for mu, nu in combinations(range(lat.dim), 2):
            p = lat.plaquette_index(x, mu, nu)
            x_mu = lat.shift(x, mu)
            x_nu = lat.shift(x, nu)
            b_mu = lat.bond_index(x, mu)
            b_nu_at_mu = lat.bond_index(x_mu, nu)
            b_mu_at_nu = lat.bond_index(x_nu, mu)
            b_nu = lat.bond_index(x, nu)
            U_mu = background[x + (mu,)]
            U_nu = background[x + (nu,)]
            d1[3*p:3*p+3, 3*b_mu:3*b_mu+3] += np.eye(3)
            d1[3*p:3*p+3, 3*b_nu_at_mu:3*b_nu_at_mu+3] += adjoint_matrix(U_mu)
            d1[3*p:3*p+3, 3*b_mu_at_nu:3*b_mu_at_nu+3] -= adjoint_matrix(U_nu)
            d1[3*p:3*p+3, 3*b_nu:3*b_nu+3] -= np.eye(3)
    return d1


def canonical_path(lat: PeriodicLattice, start: Sequence[int], end: Sequence[int]) -> list[tuple[tuple[int, ...], int, int]]:
    """Positive-coordinate canonical path; items are (site, axis, orientation)."""
    cur = tuple(start)
    out: list[tuple[tuple[int, ...], int, int]] = []
    for mu in range(lat.dim):
        steps = (end[mu] - cur[mu]) % lat.L
        for _ in range(steps):
            out.append((cur, mu, 1))
            cur = lat.shift(cur, mu)
    if cur != tuple(end):
        raise AssertionError("canonical path construction failed")
    return out


def path_transport(lat: PeriodicLattice, links: Array, path: Iterable[tuple[tuple[int, ...], int, int]]) -> Array:
    q = np.array([1.0, 0.0, 0.0, 0.0])
    for x, mu, orientation in path:
        step = links[x + (mu,)]
        q = qmul(q, step if orientation > 0 else qconj(step))
    return qnormalize(q)


def block_average_matrix(lat: PeriodicLattice, block: int, background: Array | None = None) -> tuple[PeriodicLattice, Array]:
    """Gauge-covariant block average of fine bond Lie fields.

    Each sample is transported to the block root along the canonical coordinate
    path. This is an executable reference convention pending term-by-term CMP98
    comparison; the receipt never labels it a continuum theorem.
    """
    if lat.L % block:
        raise ValueError("block size must divide L")
    coarse = PeriodicLattice(lat.L // block, lat.dim)
    if background is None:
        background = identity_links(lat)
    Q = np.zeros((3 * coarse.n_bonds, 3 * lat.n_bonds), dtype=float)
    weight = 1.0 / (block ** lat.dim)
    for c in coarse.sites():
        root = tuple(block * ci for ci in c)
        for mu in range(lat.dim):
            cb = coarse.bond_index(c, mu)
            for offset in np.ndindex((block,) * lat.dim):
                x = tuple((root[a] + offset[a]) % lat.L for a in range(lat.dim))
                fb = lat.bond_index(x, mu)
                transport = path_transport(lat, background, canonical_path(lat, root, x))
                Q[3*cb:3*cb+3, 3*fb:3*fb+3] += weight * adjoint_matrix(transport)
    return coarse, Q


def gauge_fixed_hessian(
    lat: PeriodicLattice,
    *,
    background: Array | None = None,
    gauge_weight: float = 1.0,
    average: Array | None = None,
    average_weight: float = 1.0,
) -> Array:
    d0 = coboundary_0(lat, background)
    d1 = coboundary_1(lat, background)
    H = d1.T @ d1 + gauge_weight * (d0 @ d0.T)
    if average is not None:
        H = H + average_weight * (average.T @ average)
    return 0.5 * (H + H.T)


def nullspace(A: Array, rtol: float = 1e-10) -> Array:
    A = np.asarray(A, dtype=float)
    _, s, vh = np.linalg.svd(A, full_matrices=True)
    tol = (s[0] if s.size else 1.0) * rtol
    rank = int(np.sum(s > tol))
    return vh[rank:].T.copy()


def constrained_hessian(H: Array, Q: Array, *, rtol: float = 1e-10) -> tuple[Array, Array]:
    K = nullspace(Q, rtol=rtol)
    HK = K.T @ H @ K
    return K, 0.5 * (HK + HK.T)


def conditional_covariance(H: Array, Q: Array, *, rtol: float = 1e-10) -> tuple[Array, Array, Array]:
    K, HK = constrained_hessian(H, Q, rtol=rtol)
    evals = np.linalg.eigvalsh(HK)
    if evals.size and evals[0] <= rtol:
        raise np.linalg.LinAlgError(f"restricted Hessian not positive definite: lambda_min={evals[0]:.3e}")
    CK = np.linalg.inv(HK)
    return K, CK, K @ CK @ K.T


def slogdet_positive(A: Array, *, rtol: float = 1e-12) -> tuple[float, float]:
    sign, value = np.linalg.slogdet(A)
    if sign <= 0:
        eig = np.linalg.eigvalsh(0.5 * (A + A.T))
        raise np.linalg.LinAlgError(f"matrix determinant is not positive; lambda_min={eig[0]:.3e}")
    residual = np.linalg.norm(A @ np.linalg.inv(A) - np.eye(A.shape[0]), ord=np.inf)
    if residual > math.sqrt(rtol):
        raise np.linalg.LinAlgError(f"inverse residual too large: {residual:.3e}")
    return float(value), float(residual)


def transverse_projector(lat: PeriodicLattice, momentum: Sequence[int]) -> Array:
    k = 2.0 * np.sin(np.pi * np.asarray(momentum, dtype=float) / lat.L)
    k2 = float(k @ k)
    if k2 == 0.0:
        return np.zeros((lat.dim, lat.dim))
    return k2 * np.eye(lat.dim) - np.outer(k, k)


def extract_beta_from_tensor(tensor: Array, lat: PeriodicLattice, momentum: Sequence[int]) -> dict[str, float]:
    target = transverse_projector(lat, momentum)
    denom = float(np.sum(target * target))
    beta = float(np.sum(tensor * target) / denom) if denom else float("nan")
    residual = float(np.linalg.norm(tensor - beta * target))
    k = 2.0 * np.sin(np.pi * np.asarray(momentum, dtype=float) / lat.L)
    return {"beta": beta, "fit_residual": residual, "ward_residual": float(np.linalg.norm(k @ tensor))}


def gershgorin_lower_bound(A: Array) -> float:
    A = np.asarray(A, dtype=float)
    radius = np.sum(np.abs(A), axis=1) - np.abs(np.diag(A))
    return float(np.min(np.diag(A) - radius))


def write_receipt(path: str | Path, payload: dict) -> None:
    data = {"status": "finite_computation", **payload}
    Path(path).parent.mkdir(parents=True, exist_ok=True)
    Path(path).write_text(json.dumps(data, indent=2, sort_keys=True) + "\n", encoding="utf-8")
