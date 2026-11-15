#!/usr/bin/env python3
"""Reproducible NS twin-vs-simulation benchmark; finite numerical claims only.

Uses the existing periodic Galerkin RK4 experiment as two computational twins
with different step sizes, not as independently validated physical reality.
The coarse observer hides initial phase/seed; the refined observer retains it.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

from ns_five_halves_galerkin_trajectory import run_seed

SCHEMA = "dashi.verid.ns_simulation_contact.v1"
SEEDS = (101, 202, 303)
METRICS = ("final_energy", "integrated_weighted_five_halves",
           "integrated_vorticity_fourier_l1")


def _digest(obj):
    return hashlib.sha256(json.dumps(obj, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def benchmark(steps: int = 8, dt: float = 0.002):
    if steps < 1 or not (0 < dt <= 0.01):
        raise ValueError("require steps >= 1 and 0 < dt <= 0.01")
    rows = []
    for seed in SEEDS:
        model = run_seed(seed, steps, dt)
        simulation = run_seed(seed, 2 * steps, dt / 2)
        errors = {
            key: abs(float(model[key]) - float(simulation[key]))
            for key in METRICS
        }
        rows.append({
            "seed": seed,
            "model_steps": steps,
            "simulation_steps": 2 * steps,
            "model_digest": _digest(model),
            "simulation_digest": _digest(simulation),
            "observable_errors": errors,
            "both_numerically_energy_nonincreasing": (
                model["energy_nonincreasing"] and simulation["energy_nonincreasing"]
            ),
            "contact_kind": "matched_solver_step_refinement_not_independent_physical_observation",
        })
    # This is a *predeclared* projection-stress fixture, not inferred from
    # simulation outcomes. Different hidden seed tags collide after projection.
    collision = {
        "coarse_observer": {"cutoff": 2, "viscosity": 1.0, "horizon": steps * dt},
        "hidden_worlds": [101, 202],
        "coarse_collision": True,
        "seed_coordinate_separates": True,
        "consumer_sufficiency_claim": False,
        "empirical_safety_claim": False,
    }
    report = {
        "schema": SCHEMA,
        "design": {
            "matched_seeds": list(SEEDS),
            "same_equations_same_solver": True,
            "model_method": "periodic_finite_Galerkin_RK4",
            "simulation_method": "periodic_finite_Galerkin_RK4_half_timestep",
            "comparison_horizon": steps * dt,
            "projection_stress_predeclared": "seed-hidden-vs-seed-retained",
        },
        "projection": collision,
        "comparisons": rows,
        "authority": {
            "deterministic_numerical_comparison": True,
            "independent_solver_validation": False,
            "physical_lab_validation": False,
            "continuum_error_bound": False,
            "clay_navier_stokes": False,
            "automatic_promotion": False,
        },
        "next_residual": "independent implementation, calibrated numerical error and physical-contact receipt",
    }
    report["sha256"] = _digest(report)
    return report


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--steps", type=int, default=8)
    ap.add_argument("--dt", type=float, default=0.002)
    ap.add_argument("--output-json", type=Path, required=True)
    args = ap.parse_args()
    result = benchmark(args.steps, args.dt)
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(json.dumps(result, sort_keys=True, indent=2) + "\n", encoding="utf-8")
    print(f"{SCHEMA}: {len(result['comparisons'])} pairs; digest={result['sha256']}")


if __name__ == "__main__":
    main()
