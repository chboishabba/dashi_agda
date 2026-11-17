#!/usr/bin/env python3
"""Ideal Casimir weak-field scaling ceiling.

Brown-Maclay parallel-plate energy density:
    |u| = pi^2 hbar c / (720 a^4)
gives an ideal equivalent surface mass density
    |sigma| = |u| a / c^2 = pi^2 hbar / (720 c a^3).

For an arbitrarily large sheet the Newtonian field magnitude saturates at
    g_sheet = 2 pi G |sigma|.
Thus increasing plate radius cannot exceed this fixed-gap ceiling in the
weak-field sheet model. The gap values below are inverse-design diagnostics,
not realizable material claims; at femtometre/sub-femtometre scales the ideal
perfect-conductor Casimir model is outside its engineering validity domain.
"""
from __future__ import annotations
import hashlib
import json
import math
from pathlib import Path

HBAR = 1.054571817e-34
C = 299792458.0
G = 6.67430e-11
REFERENCE_GAP_M = 100e-9
TARGETS = {
    "1e-12_m_s2": 1e-12,
    "1e-9_m_s2": 1e-9,
    "1e-6_m_s2": 1e-6,
    "1g": 9.80665,
}

def sheet_sigma_abs(gap_m: float) -> float:
    return math.pi**2 * HBAR / (720.0 * C * gap_m**3)

def sheet_g_abs(gap_m: float) -> float:
    return 2.0 * math.pi * G * sheet_sigma_abs(gap_m)

def gap_for_target_g(target_g: float) -> float:
    coefficient = 2.0 * math.pi * G * math.pi**2 * HBAR / (720.0 * C)
    return (coefficient / target_g) ** (1.0 / 3.0)

def main() -> None:
    sigma_ref = sheet_sigma_abs(REFERENCE_GAP_M)
    g_ref = sheet_g_abs(REFERENCE_GAP_M)
    inverse = {name: gap_for_target_g(value) for name, value in TARGETS.items()}

    assert g_ref < 1e-30
    assert inverse["1e-12_m_s2"] < 2e-14
    assert inverse["1e-9_m_s2"] < 2e-15
    assert inverse["1g"] < 1e-18

    script_path = Path(__file__)
    receipt = {
        "script": "scripts/casimir_ideal_sheet_scaling_ceiling.py",
        "script_sha256": hashlib.sha256(script_path.read_bytes()).hexdigest(),
        "source": {
            "brown_maclay_doi": "10.1103/PhysRev.184.1272",
            "model": "ideal parallel perfect-conductor Casimir energy + Newtonian infinite-sheet weak-field proxy",
        },
        "reference": {
            "gap_m": REFERENCE_GAP_M,
            "equivalent_surface_mass_density_kg_m2_abs": sigma_ref,
            "infinite_sheet_g_m_s2_abs": g_ref,
        },
        "inverse_gap_for_target_g_m": inverse,
        "assertions_passed": True,
        "promotion_boundaries": {
            "finite_material_realizability": False,
            "model_valid_at_femtometre_gaps": False,
            "measured_gravity": False,
            "macroscopic_negative_mass": False,
            "warp_capability": False,
        },
    }
    print(json.dumps(receipt, indent=2, sort_keys=True))

if __name__ == "__main__":
    main()
