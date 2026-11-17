#!/usr/bin/env python3
from __future__ import annotations

import math

import numpy as np


def gell_mann_half() -> list[np.ndarray]:
    i = 1j
    s3 = math.sqrt(3.0)
    lam = [
        np.array([[0, 1, 0], [1, 0, 0], [0, 0, 0]], complex),
        np.array([[0, -i, 0], [i, 0, 0], [0, 0, 0]], complex),
        np.array([[1, 0, 0], [0, -1, 0], [0, 0, 0]], complex),
        np.array([[0, 0, 1], [0, 0, 0], [1, 0, 0]], complex),
        np.array([[0, 0, -i], [0, 0, 0], [i, 0, 0]], complex),
        np.array([[0, 0, 0], [0, 0, 1], [0, 1, 0]], complex),
        np.array([[0, 0, 0], [0, 0, -i], [0, i, 0]], complex),
        np.array([[1, 0, 0], [0, 1, 0], [0, 0, -2]], complex) / s3,
    ]
    return [x / 2.0 for x in lam]


def vevs(v_32: float, v_33: float) -> tuple[np.ndarray, np.ndarray]:
    phi = np.zeros((3, 3), complex)
    chi = np.zeros((3, 3), complex)
    phi[2, 1] = v_32
    chi[2, 2] = v_33
    return phi, chi


def mass_matrix(g_l: float, g_r: float, v_32: float, v_33: float) -> np.ndarray:
    """Gram matrix of infinitesimal gauge variations on the two neutral VEVs.

    Generator order is eight SU(3)_L generators followed by eight SU(3)_R
    generators, with T_a=lambda_a/2.  Overall scalar-field normalization is
    intentionally kept as the same comparison convention as the earlier local
    receipt.
    """
    t = gell_mann_half()
    vacua = vevs(v_32, v_33)
    variations: list[tuple[np.ndarray, np.ndarray]] = []
    for generator in t:
        variations.append(tuple(g_l * generator @ v for v in vacua))
    for generator in t:
        variations.append(tuple(-g_r * v @ generator for v in vacua))

    out = np.zeros((16, 16), float)
    for a in range(16):
        for b in range(16):
            out[a, b] = sum(
                float(np.real(np.trace(x.conj().T @ y)))
                for x, y in zip(variations[a], variations[b])
            )
    return out


def neutral_discriminant(g_l: float, g_r: float, v_32: float, v_33: float) -> float:
    s = v_32 * v_32 + v_33 * v_33
    big_s = (g_l * g_l + g_r * g_r) * s
    c = (
        g_r
        * g_r
        * (4.0 * g_l * g_l + g_r * g_r)
        * v_32
        * v_32
        * v_33
        * v_33
    )
    return big_s * big_s - 3.0 * c


def neutral_eigenvalues(g_l: float, g_r: float, v_32: float, v_33: float) -> tuple[float, float]:
    s = v_32 * v_32 + v_33 * v_33
    big_s = (g_l * g_l + g_r * g_r) * s
    disc = neutral_discriminant(g_l, g_r, v_32, v_33)
    root = math.sqrt(max(0.0, disc))
    return (big_s - root) / 6.0, (big_s + root) / 6.0


def analytic_spectrum(g_l: float, g_r: float, v_32: float, v_33: float) -> list[float]:
    """Closed-form 16-mode comparison spectrum.

    Four exact zero modes are SU(2)_L plus hypercharge.  Ten positive modes
    occur in simple diagonal sectors and two are the nonzero eigenvalues of the
    neutral 3x3 block.
    """
    s = v_32 * v_32 + v_33 * v_33
    low, high = neutral_eigenvalues(g_l, g_r, v_32, v_33)
    values = [0.0] * 4
    values += [g_l * g_l * s / 4.0] * 4
    values += [g_r * g_r * v_32 * v_32 / 4.0] * 2
    values += [g_r * g_r * v_33 * v_33 / 4.0] * 2
    values += [g_r * g_r * s / 4.0] * 2
    values += [low, high]
    return sorted(values)


def verify(seed: int = 1729) -> dict[str, object]:
    rng = np.random.default_rng(seed)
    max_error = 0.0
    for _ in range(128):
        g_l, g_r, v_32, v_33 = 0.1 + 2.5 * rng.random(4)
        numeric = np.linalg.eigvalsh(mass_matrix(g_l, g_r, v_32, v_33))
        analytic = np.asarray(analytic_spectrum(g_l, g_r, v_32, v_33))
        max_error = max(max_error, float(np.max(np.abs(numeric - analytic))))
        if neutral_discriminant(g_l, g_r, v_32, v_33) < -1e-9:
            raise AssertionError("neutral discriminant became negative")

    equal_unit = analytic_spectrum(1.0, 1.0, 1.0, 1.0)
    if max_error > 2e-10:
        raise AssertionError(max_error)
    if sum(abs(x) < 1e-12 for x in equal_unit) != 4:
        raise AssertionError(equal_unit)

    return {
        "random_samples": 128,
        "maximum_numeric_vs_analytic_eigenvalue_error": max_error,
        "persistent_zero_modes": 4,
        "persistent_positive_rank": 12,
        "simple_positive_sectors": {
            "gL2_times_vsum_over_4": 4,
            "gR2_times_v32sq_over_4": 2,
            "gR2_times_v33sq_over_4": 2,
            "gR2_times_vsum_over_4": 2,
        },
        "neutral_block": "one exact Y zero mode plus lambda_minus,lambda_plus",
        "equal_unit_spectrum": equal_unit,
        "physical_couplings_or_vevs_derived": False,
    }


if __name__ == "__main__":
    for key, value in verify().items():
        print(f"{key}: {value}")
