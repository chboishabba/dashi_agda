#!/usr/bin/env python3
"""Source-bounded QTM resolution-kernel replay for Xiao et al. 2026.

Uses the reported experimental resolution coordinates:
- energy FWHM upper bound ~10 meV;
- remote-band momentum FWHM ~0.03 nm^-1.

This validates a normalized Gaussian resolution kernel on synthetic delta-like
inputs only. It is not an experimental intensity replay and does not claim the
instrument response is exactly Gaussian.
"""
from __future__ import annotations
import hashlib
import json
from pathlib import Path
import numpy as np

SOURCE_DOI = "10.1038/s41586-026-10378-x"
ENERGY_FWHM_MEV = 10.0
MOMENTUM_FWHM_INV_NM = 0.03

def sigma_from_fwhm(fwhm: float) -> float:
    return fwhm / (2.0 * np.sqrt(2.0 * np.log(2.0)))

def normalized_gaussian(grid: np.ndarray, sigma: float) -> np.ndarray:
    kernel = np.exp(-0.5 * (grid / sigma) ** 2)
    return kernel / np.trapezoid(kernel, grid)

def measured_fwhm(grid: np.ndarray, kernel: np.ndarray) -> float:
    half = float(kernel.max()) / 2.0
    indices = np.where(kernel >= half)[0]
    return float(grid[indices[-1]] - grid[indices[0]])

def main() -> None:
    energy_grid = np.linspace(-50.0, 50.0, 2001)
    momentum_grid = np.linspace(-0.15, 0.15, 2001)

    sigma_e = sigma_from_fwhm(ENERGY_FWHM_MEV)
    sigma_k = sigma_from_fwhm(MOMENTUM_FWHM_INV_NM)
    kernel_e = normalized_gaussian(energy_grid, sigma_e)
    kernel_k = normalized_gaussian(momentum_grid, sigma_k)

    integral_e = float(np.trapezoid(kernel_e, energy_grid))
    integral_k = float(np.trapezoid(kernel_k, momentum_grid))
    measured_e = measured_fwhm(energy_grid, kernel_e)
    measured_k = measured_fwhm(momentum_grid, kernel_k)

    assert abs(integral_e - 1.0) < 1e-12
    assert abs(integral_k - 1.0) < 1e-12
    assert abs(measured_e - ENERGY_FWHM_MEV) <= 0.05
    assert abs(measured_k - MOMENTUM_FWHM_INV_NM) <= 0.0002

    script_path = Path(__file__)
    receipt = {
        "script": "scripts/matbg_qtm_resolution_kernel.py",
        "script_sha256": hashlib.sha256(script_path.read_bytes()).hexdigest(),
        "source_doi": SOURCE_DOI,
        "source_resolution": {
            "energy_fwhm_upper_bound_meV": ENERGY_FWHM_MEV,
            "momentum_fwhm_inv_nm": MOMENTUM_FWHM_INV_NM,
        },
        "gaussian_model": {
            "energy_sigma_meV": float(sigma_e),
            "momentum_sigma_inv_nm": float(sigma_k),
            "energy_kernel_integral": integral_e,
            "momentum_kernel_integral": integral_k,
            "measured_energy_fwhm_meV": measured_e,
            "measured_momentum_fwhm_inv_nm": measured_k,
        },
        "assertions_passed": True,
        "promotion_boundaries": {
            "gaussian_response_is_source_measured": False,
            "experimental_intensity_arrays_used": False,
            "interacting_qtm_fit_paid": False,
            "measured_quantum_metric_paid": False,
        },
    }
    print(json.dumps(receipt, indent=2, sort_keys=True))

if __name__ == "__main__":
    main()
