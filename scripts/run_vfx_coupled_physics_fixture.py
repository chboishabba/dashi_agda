#!/usr/bin/env python3
"""Deterministic toy fixture for the coupled VFX physical-shot carrier.

This is intentionally a reduced-order regression fixture, not a CFD/FEA/EM
solver and not a calibrated claim about any fictional creature or real vessel.
It exists to exercise same-object bookkeeping across contact, water resistance,
air resistance, wake proxies, energy accounting, and optional EM routing.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
from dataclasses import asdict, dataclass


@dataclass(frozen=True)
class Inputs:
    creature_mass_kg: float
    vessel_mass_kg: float
    creature_vertical_speed_m_s: float
    water_density_kg_m3: float
    air_density_kg_m3: float
    vessel_water_cd: float
    vessel_wetted_area_m2: float
    creature_air_cd: float
    creature_frontal_area_m2: float
    dt_s: float
    em_enabled: bool
    charge_generation_mechanism: str


def qdrag(rho: float, cd: float, area: float, speed: float) -> float:
    return 0.5 * rho * cd * area * speed * abs(speed)


def run(inp: Inputs) -> dict:
    # Reduced collision coordinate: perfectly inelastic vertical coupling.
    # This intentionally exposes the lost kinetic-energy coordinate rather than
    # hiding it inside a contact solver.
    m1 = inp.creature_mass_kg
    m2 = inp.vessel_mass_kg
    v1 = inp.creature_vertical_speed_m_s
    v2 = 0.0
    p_before = m1 * v1 + m2 * v2
    v_coupled = p_before / (m1 + m2)
    p_after_contact = (m1 + m2) * v_coupled
    contact_momentum_residual = p_after_contact - p_before

    ke_before = 0.5 * m1 * v1 * v1
    ke_after_contact = 0.5 * (m1 + m2) * v_coupled * v_coupled
    contact_dissipation_j = ke_before - ke_after_contact

    water_drag_n = qdrag(
        inp.water_density_kg_m3,
        inp.vessel_water_cd,
        inp.vessel_wetted_area_m2,
        v_coupled,
    )
    air_drag_n = qdrag(
        inp.air_density_kg_m3,
        inp.creature_air_cd,
        inp.creature_frontal_area_m2,
        v_coupled,
    )

    total_mass = m1 + m2
    acceleration = -(water_drag_n + air_drag_n) / total_mass
    v_next = v_coupled + acceleration * inp.dt_s
    p_next = total_mass * v_next
    external_impulse = -(water_drag_n + air_drag_n) * inp.dt_s
    momentum_residual = p_next - (p_after_contact + external_impulse)

    # Reduced visual/physical observables. These are proxies, explicitly not a
    # free-surface Navier-Stokes solution.
    water_power_w = water_drag_n * abs(v_coupled)
    air_power_w = air_drag_n * abs(v_coupled)
    wake_energy_proxy_j = water_power_w * inp.dt_s
    air_energy_proxy_j = air_power_w * inp.dt_s

    em_admission = {
        "enabled": inp.em_enabled,
        "mechanism": inp.charge_generation_mechanism,
        "material_effect_computed": False,
        "reason": (
            "No EM force is computed by this fixture; route to Maxwell producer only "
            "when a quantitative charge/current mechanism and geometry are supplied."
        ),
    }

    result = {
        "fixture_kind": "reduced-order-vfx-coupled-physics",
        "status": "toy_fixture_not_calibrated",
        "inputs": asdict(inp),
        "contact": {
            "momentum_before_kg_m_s": p_before,
            "coupled_velocity_m_s": v_coupled,
            "momentum_residual_kg_m_s": contact_momentum_residual,
            "kinetic_energy_before_j": ke_before,
            "kinetic_energy_after_contact_j": ke_after_contact,
            "contact_dissipation_j": contact_dissipation_j,
        },
        "fluid_air_step": {
            "water_drag_n": water_drag_n,
            "air_drag_n": air_drag_n,
            "acceleration_m_s2": acceleration,
            "velocity_next_m_s": v_next,
            "momentum_residual_kg_m_s": momentum_residual,
            "wake_energy_proxy_j": wake_energy_proxy_j,
            "air_energy_proxy_j": air_energy_proxy_j,
        },
        "electromagnetism": em_admission,
        "boundaries": {
            "wake_proxy_is_full_free_surface_ns": False,
            "finite_vfx_solve_requires_ns_clay_proof": False,
            "ordinary_em_requires_yang_mills_clay_proof": False,
            "looks_right_proves_physics": False,
        },
    }
    canonical = json.dumps(result, sort_keys=True, separators=(",", ":")).encode()
    result["artifact_sha256"] = hashlib.sha256(canonical).hexdigest()
    return result


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser()
    p.add_argument("--creature-mass-kg", type=float, default=6_000_000.0)
    p.add_argument("--vessel-mass-kg", type=float, default=4_000_000.0)
    p.add_argument("--creature-vertical-speed-m-s", type=float, default=8.0)
    p.add_argument("--water-density-kg-m3", type=float, default=1025.0)
    p.add_argument("--air-density-kg-m3", type=float, default=1.225)
    p.add_argument("--vessel-water-cd", type=float, default=1.0)
    p.add_argument("--vessel-wetted-area-m2", type=float, default=1500.0)
    p.add_argument("--creature-air-cd", type=float, default=1.0)
    p.add_argument("--creature-frontal-area-m2", type=float, default=1000.0)
    p.add_argument("--dt-s", type=float, default=0.05)
    p.add_argument("--em-enabled", action="store_true")
    p.add_argument("--charge-generation-mechanism", default="none declared")
    p.add_argument("--output", default="-")
    return p.parse_args()


def main() -> int:
    a = parse_args()
    inp = Inputs(
        creature_mass_kg=a.creature_mass_kg,
        vessel_mass_kg=a.vessel_mass_kg,
        creature_vertical_speed_m_s=a.creature_vertical_speed_m_s,
        water_density_kg_m3=a.water_density_kg_m3,
        air_density_kg_m3=a.air_density_kg_m3,
        vessel_water_cd=a.vessel_water_cd,
        vessel_wetted_area_m2=a.vessel_wetted_area_m2,
        creature_air_cd=a.creature_air_cd,
        creature_frontal_area_m2=a.creature_frontal_area_m2,
        dt_s=a.dt_s,
        em_enabled=a.em_enabled,
        charge_generation_mechanism=a.charge_generation_mechanism,
    )
    if min(inp.creature_mass_kg, inp.vessel_mass_kg, inp.dt_s) <= 0:
        raise SystemExit("masses and dt must be positive")
    result = run(inp)
    text = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if a.output == "-":
        print(text, end="")
    else:
        with open(a.output, "w", encoding="utf-8") as f:
            f.write(text)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
