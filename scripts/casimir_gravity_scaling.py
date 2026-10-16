#!/usr/bin/env python3
"""Brown–Maclay ideal-plate negative-energy gravitational scaling diagnostic.

Physics source:
  Brown & Maclay, Phys. Rev. 184, 1272 (1969),
  DOI 10.1103/PhysRev.184.1272.

For ideal parallel plates, use the standard renormalized Casimir energy density
  u(a) = -pi^2 hbar c / (720 a^4).

DASHI then computes:
  rho_m = u/c^2,
  Sigma_m = rho_m * a,
and an infinite-sheet Newtonian scale
  g_sheet = 2 pi G Sigma_m.

The sheet estimate is only an order-of-magnitude weak-field proxy. It is not a
full finite-plate GR solution, a measured gravity signal, or a warp source.
"""
from __future__ import annotations
import json, math

HBAR = 1.054571817e-34
C = 299792458.0
G = 6.67430e-11
G0 = 9.80665
SEPARATIONS_M = (1e-6, 1e-7, 1e-8)


def row(a):
    energy_density = -(math.pi**2 * HBAR * C) / (720.0 * a**4)
    mass_density = energy_density / C**2
    surface_mass_density = mass_density * a
    sheet_g = 2.0 * math.pi * G * surface_mass_density
    return {
        "separation_m": a,
        "energy_density_J_m3": energy_density,
        "equivalent_mass_density_kg_m3": mass_density,
        "equivalent_surface_mass_density_kg_m2": surface_mass_density,
        "infinite_sheet_newtonian_g_m_s2": sheet_g,
        "fraction_of_standard_gravity": sheet_g / G0,
    }


def main():
    rows = [row(a) for a in SEPARATIONS_M]
    receipt = {
        "source": "10.1103/PhysRev.184.1272",
        "model": "ideal parallel-plate Brown-Maclay scaling plus DASHI weak-field sheet proxy",
        "rows": rows,
        "promotion_boundaries": {
            "finite_plate_gr_solution": False,
            "measured_gravitational_backreaction": False,
            "macroscopic_scaling_demonstrated": False,
            "warp_or_wormhole_capability": False,
        },
    }
    assert rows[1]["energy_density_J_m3"] < 0
    assert abs(rows[1]["fraction_of_standard_gravity"]) < 1e-30
    assert abs(rows[2]["infinite_sheet_newtonian_g_m_s2"]) > abs(rows[1]["infinite_sheet_newtonian_g_m_s2"])
    print(json.dumps(receipt, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
