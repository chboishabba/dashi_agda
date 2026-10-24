#!/usr/bin/env python3
"""Resolution-aware synthetic QTM forward observer for Xiao et al. 2026.

Composes DASHI's finite BM wavefunction/matrix-element observer with the
source-bounded QTM resolution coordinates. It produces a synthetic broadened
intensity surface only; no experimental arrays are ingested and no fit is
claimed.
"""
from __future__ import annotations
import hashlib
import json
from pathlib import Path
import numpy as np
import matbg_bm_plane_wave_replay as BM
import matbg_qtm_resolution_kernel as R

THETA_DEG = 1.10
W_AB_EV = 0.11
RATIO = 0.6
SHELLS = 3
Q_SAMPLES = 41

def matrix_element_observer(prepared, q_fraction: float):
    b1 = prepared[3]
    layer1 = prepared[5]
    k = q_fraction * b1
    h = BM.hamiltonian(k, THETA_DEG, prepared)
    values, vectors = np.linalg.eigh(h)
    mid = len(values) // 2
    state = vectors[:, mid]
    top_dim = 2 * len(layer1)
    top = state[:top_dim]
    factor = 0.0
    for i in range(len(layer1)):
        a, b = top[2*i:2*i+2]
        factor += float(abs(a + b) ** 2)
    return float(values[mid] * 1000.0), factor

def gaussian_density(grid: np.ndarray, center: float, sigma: float) -> np.ndarray:
    return np.exp(-0.5 * ((grid - center) / sigma) ** 2) / (sigma * np.sqrt(2.0 * np.pi))

def main() -> None:
    prepared = BM.prepare(THETA_DEG, SHELLS, W_AB_EV, RATIO)
    b1_norm = float(np.linalg.norm(prepared[3]))
    qs = np.linspace(0.0, 1.0, Q_SAMPLES)
    rows = [matrix_element_observer(prepared, float(q)) for q in qs]

    sigma_e = R.sigma_from_fwhm(R.ENERGY_FWHM_MEV)
    sigma_k = R.sigma_from_fwhm(R.MOMENTUM_FWHM_INV_NM)
    energy_grid = np.linspace(-30.0, 30.0, 601)
    momentum_grid = np.linspace(-0.05, b1_norm + 0.05, 601)
    intensity = np.zeros((len(energy_grid), len(momentum_grid)))

    for q, (energy_mev, factor) in zip(qs, rows):
        momentum = float(q) * b1_norm
        ge = gaussian_density(energy_grid, energy_mev, sigma_e)
        gk = gaussian_density(momentum_grid, momentum, sigma_k)
        intensity += factor * np.outer(ge, gk)

    integrated = float(np.trapezoid(np.trapezoid(intensity, momentum_grid, axis=1), energy_grid))
    total_weight = float(sum(factor for _, factor in rows))
    peak_index = np.unravel_index(np.argmax(intensity), intensity.shape)
    peak_energy = float(energy_grid[peak_index[0]])
    peak_momentum = float(momentum_grid[peak_index[1]])
    factors = [factor for _, factor in rows]
    energies = [energy for energy, _ in rows]

    assert abs(integrated - total_weight) < 1e-3
    assert max(factors) - min(factors) > 1e-3
    assert min(energies) < max(energies)

    script_path = Path(__file__)
    receipt = {
        "script": "scripts/matbg_qtm_resolution_aware_forward_observer.py",
        "script_sha256": hashlib.sha256(script_path.read_bytes()).hexdigest(),
        "sources": {
            "xiao2026": "10.1038/s41586-026-10378-x",
            "bm2011": "10.1073/pnas.1108174108",
        },
        "model": {
            "theta_deg": THETA_DEG,
            "wAB_eV_generic_reference": W_AB_EV,
            "w0_over_w1_source_ratio": RATIO,
            "shells": SHELLS,
            "q_samples": Q_SAMPLES,
            "b1_norm_inv_nm": b1_norm,
        },
        "resolution": {
            "energy_fwhm_upper_bound_meV": R.ENERGY_FWHM_MEV,
            "momentum_fwhm_inv_nm": R.MOMENTUM_FWHM_INV_NM,
            "gaussian_energy_sigma_meV": float(sigma_e),
            "gaussian_momentum_sigma_inv_nm": float(sigma_k),
        },
        "synthetic_surface": {
            "integrated_intensity": integrated,
            "unbroadened_total_matrix_element_weight": total_weight,
            "peak_energy_meV": peak_energy,
            "peak_momentum_inv_nm": peak_momentum,
            "factor_min": float(min(factors)),
            "factor_max": float(max(factors)),
            "central_band_energy_min_meV": float(min(energies)),
            "central_band_energy_max_meV": float(max(energies)),
        },
        "assertions_passed": True,
        "promotion_boundaries": {
            "experimental_arrays_used": False,
            "gaussian_response_source_measured": False,
            "absolute_wAB_sample_calibrated": False,
            "interacting_self_energy_included": False,
            "experimental_fit_paid": False,
        },
    }
    print(json.dumps(receipt, indent=2, sort_keys=True))

if __name__ == "__main__":
    main()
