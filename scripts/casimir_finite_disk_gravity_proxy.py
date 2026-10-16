#!/usr/bin/env python3
"""Finite-radius weak-field Casimir gravity proxy.

Uses Brown-Maclay ideal parallel-plate energy density and replaces the
infinite-sheet gravitational proxy with the Newtonian on-axis field of a thin
uniform disk carrying the equivalent surface mass density. This is an
order-of-magnitude diagnostic, not a finite-plate GR solution or measurement.
"""

import json
import math

HBAR = 1.054571817e-34
C = 299792458.0
G = 6.67430e-11
G0 = 9.80665
SEPARATION_M = 100e-9
RADIUS_M = 0.01
AXIS_Z_M = 0.001

energy_density = -(math.pi**2 * HBAR * C) / (720.0 * SEPARATION_M**4)
mass_density = energy_density / C**2
surface_mass_density = mass_density * SEPARATION_M
infinite_sheet_acceleration = 2.0 * math.pi * G * surface_mass_density
finite_disk_factor = 1.0 - AXIS_Z_M / math.sqrt(AXIS_Z_M**2 + RADIUS_M**2)
finite_disk_acceleration = infinite_sheet_acceleration * finite_disk_factor

assert 0.0 < finite_disk_factor < 1.0
assert abs(finite_disk_acceleration) < abs(infinite_sheet_acceleration)

evidence = {
    "model": "Brown-Maclay ideal Casimir energy with finite-disk Newtonian weak-field proxy",
    "source_doi": "10.1103/PhysRev.184.1272",
    "separation_m": SEPARATION_M,
    "disk_radius_m": RADIUS_M,
    "axis_z_m": AXIS_Z_M,
    "energy_density_J_m3": energy_density,
    "equivalent_mass_density_kg_m3": mass_density,
    "equivalent_surface_mass_density_kg_m2": surface_mass_density,
    "infinite_sheet_acceleration_m_s2": infinite_sheet_acceleration,
    "finite_disk_factor": finite_disk_factor,
    "finite_disk_acceleration_m_s2": finite_disk_acceleration,
    "finite_disk_fraction_g": finite_disk_acceleration / G0,
    "assertions_passed": True,
    "promotion_boundaries": {
        "finite_plate_gr_solution": False,
        "measured_gravity": False,
        "macroscopic_scaling": False,
        "warp_capability": False,
        "wormhole_capability": False,
        "agda_kernel_receipt": False
    }
}

print(json.dumps(evidence, indent=2, sort_keys=True))
