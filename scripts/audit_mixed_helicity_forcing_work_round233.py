#!/usr/bin/env python3
"""Round233 diagnostic: sign of actual NS mixed-helicity forcing work.

This is exploratory/falsification code, not proof authority.  It constructs
finite real divergence-free Fourier fields on a cube, applies the Leray-
projected quadratic Navier--Stokes nonlinearity, forms

    M_k = sum_{p+q=k} u_p^+ x u_q^-

and its product-rule nonlinear forcing F_k^{+-}, then evaluates

    W = sum_k Re <M_k, F_k^{+-}>.

The decision question is whether W has a universal nonpositive sign.  Finding
both signs falsifies a direct Lyapunov route.  The audit also records the
homogeneity: under u -> lambda u, M -> lambda^2 M, F^{+-} -> lambda^3 F^{+-},
so W -> lambda^5 W, while viscous quadratic-defect damping is quartic.
"""

from __future__ import annotations

import itertools
import random
from typing import Dict, Iterable, Tuple

import numpy as np

Mode = Tuple[int, int, int]
Vector = np.ndarray


def leray(k: Mode, v: Vector) -> Vector:
    kk = float(sum(x * x for x in k))
    if kk == 0.0:
        return np.zeros(3, dtype=np.complex128)
    kv = np.asarray(k, dtype=float)
    return v - kv * (np.dot(kv, v) / kk)


def normalized_curl(k: Mode, v: Vector) -> Vector:
    r2 = float(sum(x * x for x in k))
    if r2 == 0.0:
        return np.zeros(3, dtype=np.complex128)
    return 1j * np.cross(np.asarray(k, dtype=float), v) / np.sqrt(r2)


def hplus(k: Mode, v: Vector) -> Vector:
    return 0.5 * (leray(k, v) + normalized_curl(k, v))


def hminus(k: Mode, v: Vector) -> Vector:
    return 0.5 * (leray(k, v) - normalized_curl(k, v))


def sub(a: Mode, b: Mode) -> Mode:
    return tuple(a[j] - b[j] for j in range(3))  # type: ignore[return-value]


def neg(k: Mode) -> Mode:
    return (-k[0], -k[1], -k[2])


def nonlinear_forcing(modes: list[Mode], u: Dict[Mode, Vector], k: Mode) -> Vector:
    # Fourier convention: N_k = -i P_k sum_{p+q=k} (u_p . q) u_q.
    total = np.zeros(3, dtype=np.complex128)
    for p in modes:
        q = sub(k, p)
        if q in u:
            total += np.dot(u[p], np.asarray(q, dtype=float)) * u[q]
    return -1j * leray(k, total)


def mixed_output(modes: list[Mode], u: Dict[Mode, Vector], k: Mode) -> Vector:
    total = np.zeros(3, dtype=np.complex128)
    for p in modes:
        q = sub(k, p)
        if q in u:
            total += np.cross(hplus(p, u[p]), hminus(q, u[q]))
    return total


def mixed_forcing_output(
    modes: list[Mode], u: Dict[Mode, Vector], forcing: Dict[Mode, Vector], k: Mode
) -> Vector:
    total = np.zeros(3, dtype=np.complex128)
    for p in modes:
        q = sub(k, p)
        if q in u:
            total += np.cross(hplus(p, forcing[p]), hminus(q, u[q]))
            total += np.cross(hplus(p, u[p]), hminus(q, forcing[q]))
    return total


def random_real_divergence_free_field(radius: int, density: float) -> tuple[list[Mode], Dict[Mode, Vector]]:
    modes = [
        k for k in itertools.product(range(-radius, radius + 1), repeat=3)
        if k != (0, 0, 0)
    ]
    u: Dict[Mode, Vector] = {}
    visited: set[Mode] = set()
    for k in modes:
        if k in visited:
            continue
        nk = neg(k)
        if random.random() <= density:
            raw = np.asarray(
                [random.gauss(0.0, 1.0) + 1j * random.gauss(0.0, 1.0) for _ in range(3)],
                dtype=np.complex128,
            )
            value = leray(k, raw)
        else:
            value = np.zeros(3, dtype=np.complex128)
        u[k] = value
        u[nk] = np.conjugate(value)
        visited.add(k)
        visited.add(nk)
    return modes, u


def forcing_work(modes: list[Mode], u: Dict[Mode, Vector]) -> tuple[float, float]:
    forcing = {k: nonlinear_forcing(modes, u, k) for k in modes}
    work = 0.0
    mass = 0.0
    for k in modes:
        m = mixed_output(modes, u, k)
        f = mixed_forcing_output(modes, u, forcing, k)
        work += float(np.real(np.vdot(m, f)))
        mass += float(np.real(np.vdot(m, m)))
    return work, mass


def scale_field(u: Dict[Mode, Vector], lam: float) -> Dict[Mode, Vector]:
    return {k: lam * v for k, v in u.items()}


def main() -> None:
    random.seed(233)
    np.random.seed(233)

    samples: list[tuple[float, float]] = []
    positive_example = None
    for _ in range(80):
        modes, u = random_real_divergence_free_field(radius=1, density=0.55)
        work, mass = forcing_work(modes, u)
        samples.append((work, mass))
        if work > 1e-8 and positive_example is None:
            positive_example = (modes, u, work)

    works = [w for w, _ in samples]
    print("Round233 physical mixed-helicity forcing-work audit")
    print(f"samples: {len(samples)}")
    print(f"min forcing work: {min(works): .12e}")
    print(f"max forcing work: {max(works): .12e}")
    print(f"mean forcing work:{sum(works)/len(works): .12e}")

    if not (min(works) < -1e-8 and max(works) > 1e-8):
        raise AssertionError("expected both signs in physical forcing-work audit")

    if positive_example is None:
        raise AssertionError("no positive forcing-work witness found")

    modes, u, base_work = positive_example
    w2, _ = forcing_work(modes, scale_field(u, 2.0))
    w3, _ = forcing_work(modes, scale_field(u, 3.0))
    ratio2 = w2 / base_work
    ratio3 = w3 / base_work
    print(f"positive witness W: {base_work: .12e}")
    print(f"W(2u)/W(u): {ratio2: .12f} (expected 32)")
    print(f"W(3u)/W(u): {ratio3: .12f} (expected 243)")

    if abs(ratio2 - 32.0) > 1e-8 or abs(ratio3 - 243.0) > 1e-7:
        raise AssertionError("forcing-work homogeneity is not quintic")

    print("DECISION:")
    print("  Actual projected NS mixed-helicity forcing work has both signs.")
    print("  Therefore no universal nonpositive forcing-work Lyapunov law exists.")
    print("  Positive nonlinear work is quintic in amplitude; viscous Q damping is quartic.")
    print("  Completion must use time-integrated trajectory rigidity/correlation, not pointwise sign.")


if __name__ == "__main__":
    main()
