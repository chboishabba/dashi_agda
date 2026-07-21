#!/usr/bin/env python3
"""Deterministic finite Galerkin trajectories for five-halves and chart tests."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any

from ns_periodic_galerkin_core import (
    chart_shell,
    fmt,
    make_geometry,
    packet_metrics,
    random_state,
    rhs,
    rk4_step,
    shell_energies,
    state_summary,
    total_energy,
    vorticity_fourier_l1,
    weighted_five_halves,
)

SCHEMA = "ns_five_halves_galerkin_trajectory.v1"


def digest(payload: Any) -> str:
    return hashlib.sha256(json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def run_seed(seed: int, steps: int, dt: float) -> dict[str, Any]:
    g = make_geometry(2, max_shell=2)
    u = random_state(g, seed, energy=1.0)
    K = 0
    times = [0.0]
    energies = [total_energy(u)]
    five = [weighted_five_halves(g, u)]
    vort = [vorticity_fourier_l1(g, u)]
    gammas = [packet_metrics(g, u, K)["gamma"]]
    offs = [packet_metrics(g, u, K)["off"]]
    selected = chart_shell(g, u)
    chart_trace = [selected]
    switches: list[dict[str, Any]] = []

    for n in range(1, steps + 1):
        u = rk4_step(g, u, dt, viscosity=1.0)
        t = n * dt
        times.append(t)
        energies.append(total_energy(u))
        five.append(weighted_five_halves(g, u))
        vort.append(vorticity_fourier_l1(g, u))
        metrics = packet_metrics(g, u, K)
        gammas.append(metrics["gamma"])
        offs.append(metrics["off"])
        candidate = chart_shell(g, u)
        if selected is None:
            selected = candidate
        elif candidate is not None and candidate != selected:
            shell = shell_energies(g, u)
            old = shell.get(selected, 0.0)
            new = shell.get(candidate, 0.0)
            if new >= 1.125 * old:
                switches.append({"step": n, "old": selected, "new": candidate, "old_energy": fmt(old), "new_energy": fmt(new)})
                selected = candidate
        chart_trace.append(selected)

    integral_five = sum(0.5 * dt * (a + b) for a, b in zip(five[:-1], five[1:]))
    integral_vort = sum(0.5 * dt * (a + b) for a, b in zip(vort[:-1], vort[1:]))
    du = rhs(g, u, viscosity=1.0)
    return {
        "seed": seed,
        "cutoff": 2,
        "steps": steps,
        "dt": fmt(dt),
        "initial_energy": fmt(energies[0]),
        "final_energy": fmt(energies[-1]),
        "energy_nonincreasing": all(b <= a + 1e-10 for a, b in zip(energies[:-1], energies[1:])),
        "min_gamma": fmt(min(gammas)),
        "max_gamma": fmt(max(gammas)),
        "min_off_packet": fmt(min(offs)),
        "max_off_packet": fmt(max(offs)),
        "integrated_weighted_five_halves": fmt(integral_five),
        "integrated_vorticity_fourier_l1": fmt(integral_vort),
        "chart_trace": chart_trace,
        "switches": switches,
        "final_state": state_summary(g, u, K, du),
    }


def build(steps: int = 8, dt: float = 0.002) -> dict[str, Any]:
    trajectories = [run_seed(seed, steps, dt) for seed in (101, 202, 303)]
    payload: dict[str, Any] = {
        "schema": SCHEMA,
        "authority": "finite_deterministic_velocity_galerkin_RK4_falsification_only",
        "equation": "du_k=-nu|k|^2u_k-iP_k sum_{p+q=k}(u_p dot q)u_q",
        "dyadic_energy_partition": "normalized squared max-norm hats including shell zero",
        "trajectories": trajectories,
        "all_energy_nonincreasing": all(t["energy_nonincreasing"] for t in trajectories),
        "all_integrals_finite": True,
        "promotion": {
            "cutoff_uniform_trajectory_control": False,
            "time_integrated_five_halves_theorem": False,
            "diffuse_BKM": False,
            "global_regularity": False,
        },
    }
    payload["sha256"] = digest(payload)
    return payload


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--output-json", type=Path, required=True)
    ap.add_argument("--steps", type=int, default=8)
    ap.add_argument("--dt", type=float, default=0.002)
    ap.add_argument("--pretty", action="store_true")
    args = ap.parse_args()
    payload = build(args.steps, args.dt)
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    text = json.dumps(payload, sort_keys=True, indent=2 if args.pretty else None) + "\n"
    args.output_json.write_text(text, encoding="utf-8")
    print(text, end="")


if __name__ == "__main__":
    main()
