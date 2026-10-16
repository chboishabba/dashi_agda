#!/usr/bin/env python3
"""Single-point coupled THF Hubbard-I Green-function reference.

Uses Xiao et al. Nature 653 (2026), DOI 10.1038/s41586-026-10378-x,
at a deliberately explicit neutrality fixture:
  k = 0, nu_f = 0, mu = mu_c = mu_f = delta_mu = 0.
The source parameters used are gamma=-70 meV, M=3.7 meV, U=60 meV and
lifetime broadening tau^-1=1 meV.

The 6x6 block inverse is
  [[(Gc0)^-1, H_cf],
   [H_cf^dagger, (Gf0)^-1]]
with the k=0 literal Hc/Hcf matrices already formalized in DASHI.

This is a coupled-propagator execution fixture only. It does not integrate
over k/omega to determine densities, solve mu self-consistently, fit QTM data,
or identify the paper's V/Y notation.
"""

from __future__ import annotations
import hashlib
import json
from pathlib import Path
import numpy as np

U_MEV = 60.0
GAMMA_MEV = -70.0
M_MEV = 3.7
ETA_MEV = 1.0


def gf0_scalar(omega_mev: float) -> complex:
    return (
        0.5 / (omega_mev + U_MEV / 2.0 + 1j * ETA_MEV)
        + 0.5 / (omega_mev - U_MEV / 2.0 + 1j * ETA_MEV)
    )


def coupled_green(omega_mev: float):
    hc = np.zeros((4, 4), dtype=complex)
    hc[2, 3] = M_MEV
    hc[3, 2] = M_MEV

    hcf = np.zeros((4, 2), dtype=complex)
    hcf[0, 0] = GAMMA_MEV
    hcf[1, 1] = GAMMA_MEV

    gc0_inverse = (omega_mev + 1j * ETA_MEV) * np.eye(4) - hc
    gf0_inverse = (1.0 / gf0_scalar(omega_mev)) * np.eye(2)

    inverse_block = np.block(
        [[gc0_inverse, hcf], [hcf.conj().T, gf0_inverse]]
    )
    green = np.linalg.inv(inverse_block)
    gc = green[:4, :4]
    gf = green[4:, 4:]

    ac = float(-np.imag(np.trace(gc)) / np.pi)
    af = float(-np.imag(np.trace(gf)) / np.pi)
    inversion_error = float(
        np.max(np.abs(inverse_block @ green - np.eye(6)))
    )
    return ac, af, inversion_error


def main():
    omega_grid = np.linspace(-120.0, 120.0, 4801)
    rows = []
    for omega in omega_grid:
        ac, af, err = coupled_green(float(omega))
        rows.append((float(omega), ac, af, err))

    f_peak = max(rows, key=lambda row: row[2])
    c_high_peak = max((row for row in rows if row[0] > 20.0), key=lambda row: row[1])
    c_low_peak = max((row for row in rows if -20.0 <= row[0] <= 20.0), key=lambda row: row[1])
    zero = min(rows, key=lambda row: abs(row[0]))

    max_inversion_error = max(row[3] for row in rows)
    assert max_inversion_error < 1e-12
    assert abs(abs(f_peak[0]) - 76.15) < 0.1
    assert abs(c_high_peak[0] - 76.15) < 0.1
    assert abs(abs(c_low_peak[0]) - 3.7) < 0.1
    assert zero[2] < 1e-3

    script_path = Path(__file__)
    receipt = {
        "script": "scripts/matbg_thf_coupled_green_reference.py",
        "script_sha256": hashlib.sha256(script_path.read_bytes()).hexdigest(),
        "source_doi": "10.1038/s41586-026-10378-x",
        "fixture": {
            "k_nm_inverse": [0.0, 0.0],
            "nu_f": 0,
            "mu_meV": 0.0,
            "mu_c_meV": 0.0,
            "mu_f_meV": 0.0,
            "delta_mu_meV": 0.0,
            "gamma_meV": GAMMA_MEV,
            "M_meV": M_MEV,
            "U_meV": U_MEV,
            "tau_inverse_meV": ETA_MEV,
        },
        "matrix_dimension": 6,
        "max_inverse_residual": max_inversion_error,
        "dominant_f_peak": {
            "omega_meV": f_peak[0],
            "A_f": f_peak[2],
        },
        "positive_energy_c_peak": {
            "omega_meV": c_high_peak[0],
            "A_c": c_high_peak[1],
        },
        "low_energy_c_peak": {
            "omega_meV": c_low_peak[0],
            "A_c": c_low_peak[1],
        },
        "neutrality_omega_zero": {
            "A_c": zero[1],
            "A_f": zero[2],
        },
        "assertions_passed": True,
        "promotion_boundaries": {
            "density_integrals": False,
            "self_consistent_mu_nf_nc": False,
            "bz_cutoff_calibrated": False,
            "qtm_data_fit": False,
            "same_sample_entropy": False,
            "agda_kernel_receipt": False,
        },
    }
    print(json.dumps(receipt, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
