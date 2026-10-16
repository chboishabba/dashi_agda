#!/usr/bin/env python3
"""Deterministic first-shell Bistritzer–MacDonald numerical receipt.

Authority boundaries:
- Bistritzer & MacDonald (PNAS 2011, DOI 10.1073/pnas.1108174108)
  supply the first-shell/8-band continuum construction and analytic velocity
  ratio for the equal-tunnelling model.
- Xiao et al. (Nature 653, 68–75, 2026,
  DOI 10.1038/s41586-026-10378-x) supply the wavefunction-matrix-element
  best-fit ratio w0/w1 = 0.6.
- This script is a DASHI numerical reconstruction in dimensionless units.
  It is not the full converged plane-wave BM model, an interacting model,
  a same-sample QTM replay, or an experimental calibration.
"""

from __future__ import annotations
import json
import math
import numpy as np

ALPHA_MAGIC = 1.0 / math.sqrt(3.0)
QTM_W0_W1 = 0.6
DK = 1.0e-6

SIGMA_X = np.array([[0.0, 1.0], [1.0, 0.0]], dtype=complex)
SIGMA_Y = np.array([[0.0, -1.0j], [1.0j, 0.0]], dtype=complex)

Q = (
    np.array([0.0, -1.0]),
    np.array([math.sqrt(3.0) / 2.0, 0.5]),
    np.array([-math.sqrt(3.0) / 2.0, 0.5]),
)


def tunnelling_matrices(ratio: float) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    phi = 2.0 * math.pi / 3.0
    w1 = 1.0
    w0 = ratio
    return (
        np.array([[w0, w1], [w1, w0]], dtype=complex),
        np.array(
            [[w0, w1 * np.exp(-1.0j * phi)],
             [w1 * np.exp(+1.0j * phi), w0]],
            dtype=complex,
        ),
        np.array(
            [[w0, w1 * np.exp(+1.0j * phi)],
             [w1 * np.exp(-1.0j * phi), w0]],
            dtype=complex,
        ),
    )


def dirac_block(momentum: np.ndarray, alpha: float) -> np.ndarray:
    # Dimensionless choice: |q_j| = w1 = 1, hence hbar*v*k_theta = 1/alpha.
    hv = 1.0 / alpha
    return -hv * (momentum[0] * SIGMA_X + momentum[1] * SIGMA_Y)


def bm_first_shell(kx: float, ky: float, alpha: float, ratio: float) -> np.ndarray:
    """8x8 central-spinor + three first-shell spinors."""
    k = np.array([kx, ky])
    t = tunnelling_matrices(ratio)
    h = np.zeros((8, 8), dtype=complex)
    h[0:2, 0:2] = dirac_block(k, alpha)
    for j in range(3):
        block = slice(2 + 2 * j, 4 + 2 * j)
        h[block, block] = dirac_block(k + Q[j], alpha)
        h[0:2, block] = t[j]
        h[block, 0:2] = t[j].conj().T
    return h


def analytic_equal_tunnelling_velocity_ratio(alpha: float) -> float:
    a2 = alpha * alpha
    return (1.0 - 3.0 * a2) / (1.0 + 6.0 * a2)


def numeric_velocity_ratio(alpha: float, ratio: float, dk: float = DK) -> float:
    eig = np.linalg.eigvalsh(bm_first_shell(dk, 0.0, alpha, ratio))
    positive_central = eig[4]
    bare_hv = 1.0 / alpha
    return float(positive_central / (bare_hv * dk))


def central_zero_mode_error(alpha: float, ratio: float) -> float:
    eig = np.linalg.eigvalsh(bm_first_shell(0.0, 0.0, alpha, ratio))
    return float(max(abs(eig[3]), abs(eig[4])))


def hermiticity_error(alpha: float, ratio: float) -> float:
    h = bm_first_shell(0.137, -0.091, alpha, ratio)
    return float(np.max(np.abs(h - h.conj().T)))


def main() -> None:
    alpha_check = 0.45
    analytic = analytic_equal_tunnelling_velocity_ratio(alpha_check)
    numerical = numeric_velocity_ratio(alpha_check, 1.0)
    equal_model_magic = numeric_velocity_ratio(ALPHA_MAGIC, 1.0)
    qtm_ratio_magic = numeric_velocity_ratio(ALPHA_MAGIC, QTM_W0_W1)

    receipt = {
        "model": "BM first-shell 8-band dimensionless reconstruction",
        "sources": {
            "bm2011": "10.1073/pnas.1108174108",
            "xiao2026_qtm_ratio": "10.1038/s41586-026-10378-x",
        },
        "inputs": {
            "alpha_magic": ALPHA_MAGIC,
            "qtm_w0_over_w1": QTM_W0_W1,
            "finite_difference_dk": DK,
        },
        "checks": {
            "hermiticity_error_qtm_ratio": hermiticity_error(ALPHA_MAGIC, QTM_W0_W1),
            "zero_mode_error_equal": central_zero_mode_error(ALPHA_MAGIC, 1.0),
            "zero_mode_error_qtm_ratio": central_zero_mode_error(ALPHA_MAGIC, QTM_W0_W1),
            "analytic_velocity_ratio_alpha_0p45": analytic,
            "numeric_velocity_ratio_alpha_0p45": numerical,
            "analytic_numeric_abs_error": abs(analytic - numerical),
            "numeric_magic_velocity_ratio_equal": equal_model_magic,
            "numeric_magic_velocity_ratio_qtm_ratio": qtm_ratio_magic,
        },
        "promotion_boundaries": {
            "full_plane_wave_convergence": False,
            "absolute_sample_tunnelling_scale": False,
            "interacting_self_energy": False,
            "qtm_data_replay": False,
            "same_sample_entropy": False,
        },
    }

    assert receipt["checks"]["hermiticity_error_qtm_ratio"] < 1e-13
    assert receipt["checks"]["zero_mode_error_equal"] < 1e-12
    assert receipt["checks"]["zero_mode_error_qtm_ratio"] < 1e-12
    assert receipt["checks"]["analytic_numeric_abs_error"] < 1e-6
    assert abs(receipt["checks"]["numeric_magic_velocity_ratio_equal"]) < 1e-5
    assert abs(receipt["checks"]["numeric_magic_velocity_ratio_qtm_ratio"]) < 1e-5

    print(json.dumps(receipt, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
