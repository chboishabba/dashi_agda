#!/usr/bin/env python3
"""Finite-grid THF self-consistency obstruction replay for Xiao et al. 2026.

This intentionally does not claim the published self-consistent solution.
It evaluates the source equations on a small explicit quadrature fixture and
shows that the best residual depends materially on unresolved BZ/cutoff and
V-versus-Y notation choices. That is evidence that the remaining full solve
needs a licensed normalization/discretization rather than another generic type.
"""
import json
import numpy as np

VSTAR = -1000.0
VSTAR_PRIME = 366.0
GAMMA = -70.0
M = 3.7
U = 60.0
W = 45.0
ETA = 1.0
N = 8.0
OMEGAS = np.linspace(-140.0, 0.0, 101)
NU = 0.5

def matrices(kmax):
    ks = np.linspace(-kmax, kmax, 3)
    out = []
    for kx in ks:
        for ky in ks:
            k = complex(kx, ky)
            kb = np.conj(k)
            hc = np.array([
                [0, 0, VSTAR*k, 0],
                [0, 0, 0, VSTAR*kb],
                [VSTAR*kb, 0, 0, M],
                [0, VSTAR*k, M, 0],
            ], dtype=complex)
            hcf = np.array([
                [GAMMA, VSTAR_PRIME*kb],
                [VSTAR_PRIME*k, GAMMA],
                [0, 0],
                [0, 0],
            ], dtype=complex)
            out.append((hc, hcf))
    return out

def raw_occupations(mu, dnf, dnc, nu, v_capital, mats):
    nu_f = np.sign(nu) * np.floor(abs(nu))
    mu_f = mu - W*dnc
    mu_c = mu - W*dnf - v_capital*dnc
    delta_mu = mu_f - nu*U
    a_f = []
    a_c = []
    for omega in OMEGAS:
        gf0 = (
            (0.5 + nu_f/N)/(omega + delta_mu + U/2 + 1j*ETA)
            + (0.5 - nu_f/N)/(omega + delta_mu - U/2 + 1j*ETA)
        )
        gf0_inv = (1.0/gf0) * np.eye(2)
        af = 0.0
        ac = 0.0
        for hc, hcf in mats:
            block = np.empty((6, 6), dtype=complex)
            block[:4, :4] = (omega + mu_c + 1j*ETA)*np.eye(4) - hc
            block[:4, 4:] = hcf
            block[4:, :4] = hcf.conj().T
            block[4:, 4:] = gf0_inv
            green = np.linalg.inv(block)
            ac += -np.imag(np.trace(green[:4, :4]))/np.pi
            af += -np.imag(np.trace(green[4:, 4:]))/np.pi
        a_c.append(ac/len(mats))
        a_f.append(af/len(mats))
    return (
        4*np.trapezoid(a_f, OMEGAS),
        4*np.trapezoid(a_c, OMEGAS),
    )

def best_residual(kmax, v_capital):
    mats = matrices(kmax)
    baseline_f, baseline_c = raw_occupations(0.0, 0.0, 0.0, 0.0, v_capital, mats)
    best = None
    for dnf in np.linspace(-0.15, 0.35, 6):
        dnc = NU/4.0 - dnf
        for mu in np.linspace(-10.0, 30.0, 9):
            occ_f, occ_c = raw_occupations(mu, dnf, dnc, NU, v_capital, mats)
            rf = dnf - (occ_f - baseline_f)
            rc = dnc - (occ_c - baseline_c)
            norm = float(np.hypot(rf, rc))
            row = {
                "residual_norm": norm,
                "delta_n_f": float(dnf),
                "delta_n_c": float(dnc),
                "mu_meV": float(mu),
                "residual_f": float(rf),
                "residual_c": float(rc),
                "baseline_f": float(baseline_f),
                "baseline_c": float(baseline_c),
            }
            if best is None or norm < best["residual_norm"]:
                best = row
    return best

cases = [
    {"kmax_nm_inverse": 0.04, "V_meV": 0.0},
    {"kmax_nm_inverse": 0.04, "V_meV": 45.0},
    {"kmax_nm_inverse": 0.08, "V_meV": 45.0},
]
for case in cases:
    case["best"] = best_residual(case["kmax_nm_inverse"], case["V_meV"])

assert all(case["best"]["residual_norm"] > 0.1 for case in cases)
assert abs(cases[1]["best"]["residual_norm"] - cases[2]["best"]["residual_norm"]) > 0.4

print(json.dumps({
    "model": "finite-grid THF self-consistency obstruction replay",
    "source_doi": "10.1038/s41586-026-10378-x",
    "target_total_filling": NU,
    "grid": {
        "k_points_per_axis": 3,
        "omega_points": len(OMEGAS),
        "omega_window_meV": [float(OMEGAS[0]), float(OMEGAS[-1])],
        "delta_n_f_grid": [-0.15, -0.05, 0.05, 0.15, 0.25, 0.35],
        "mu_grid_meV": [-10, -5, 0, 5, 10, 15, 20, 25, 30],
    },
    "cases": cases,
    "assertions_passed": True,
    "interpretation": "coarse finite quadrature does not close self-consistency and is strongly cutoff/notation sensitive; full source-faithful solve remains normalization/discretization gated",
    "promotion_boundaries": {
        "full_self_consistent_solution": False,
        "source_identifies_V_with_Y": False,
        "qtm_experimental_fit": False,
        "same_sample_entropy": False,
    }
}, indent=2))
