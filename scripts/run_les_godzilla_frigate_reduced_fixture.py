#!/usr/bin/env python3
"""Deterministic reduced-order LES/VFX multiphysics fixture.

This is a regression producer, not an authoritative naval/structural/CFD model.
It intentionally uses simple lumped formulas so the staged LES admission surface
has a concrete artifact to compare against higher-fidelity backends later.

Stages mirror DASHI.Environment.LESGodzillaFrigateStagedExecutionExact:
contact -> structure -> water -> air -> secondary phase -> acoustics -> EM -> optics.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path


@dataclass(frozen=True)
class Inputs:
    dt_s: float = 0.02
    creature_mass_kg: float = 6.0e7
    creature_speed_m_s: float = 8.0
    hull_effective_mass_kg: float = 4.0e6
    contact_restitution: float = 0.05
    structural_energy_fraction: float = 0.35
    water_density_kg_m3: float = 1025.0
    water_drag_coefficient: float = 0.9
    wetted_reference_area_m2: float = 1800.0
    air_density_kg_m3: float = 1.225
    air_drag_coefficient: float = 1.1
    creature_frontal_area_m2: float = 2500.0
    acoustic_fraction: float = 0.015
    spray_fraction: float = 0.08
    em_fraction: float = 1.0e-8


@dataclass(frozen=True)
class Ledger:
    reduced_mass_kg: float
    impact_impulse_N_s: float
    contact_energy_J: float
    structural_dissipation_J: float
    hull_post_contact_speed_m_s: float
    water_drag_force_N: float
    water_drag_work_J: float
    air_drag_force_N: float
    air_drag_work_J: float
    spray_energy_J: float
    acoustic_energy_J: float
    em_bookkeeping_energy_J: float
    residual_energy_J: float
    residual_energy_relative: float
    momentum_reference_kg_m_s: float
    wake_momentum_increment_kg_m_s: float


def simulate(inp: Inputs) -> Ledger:
    # 1-D two-body reduced-mass collision surrogate.
    m1 = inp.creature_mass_kg
    m2 = inp.hull_effective_mass_kg
    mu = (m1 * m2) / (m1 + m2)
    relative_speed = inp.creature_speed_m_s
    impulse = (1.0 + inp.contact_restitution) * mu * relative_speed
    contact_energy = 0.5 * mu * relative_speed**2

    structural = inp.structural_energy_fraction * contact_energy
    post_structural = max(contact_energy - structural, 0.0)
    hull_speed = math.sqrt(max(2.0 * post_structural / m2, 0.0))

    # Reduced-order quadratic resistance terms over one staged time step.
    water_drag = 0.5 * inp.water_density_kg_m3 * inp.water_drag_coefficient * inp.wetted_reference_area_m2 * hull_speed**2
    water_work = water_drag * hull_speed * inp.dt_s

    air_drag = 0.5 * inp.air_density_kg_m3 * inp.air_drag_coefficient * inp.creature_frontal_area_m2 * relative_speed**2
    air_work = air_drag * relative_speed * inp.dt_s

    # Secondary observer-facing channels are explicit fractions of the contact
    # event, not claimed physical constitutive laws.
    spray = inp.spray_fraction * contact_energy
    acoustic = inp.acoustic_fraction * contact_energy
    em_energy = inp.em_fraction * contact_energy

    accounted = structural + water_work + air_work + spray + acoustic + em_energy
    residual = contact_energy - accounted
    relative_residual = abs(residual) / contact_energy if contact_energy else 0.0

    momentum_ref = mu * relative_speed
    wake_momentum = water_drag * inp.dt_s

    return Ledger(
        reduced_mass_kg=mu,
        impact_impulse_N_s=impulse,
        contact_energy_J=contact_energy,
        structural_dissipation_J=structural,
        hull_post_contact_speed_m_s=hull_speed,
        water_drag_force_N=water_drag,
        water_drag_work_J=water_work,
        air_drag_force_N=air_drag,
        air_drag_work_J=air_work,
        spray_energy_J=spray,
        acoustic_energy_J=acoustic,
        em_bookkeeping_energy_J=em_energy,
        residual_energy_J=residual,
        residual_energy_relative=relative_residual,
        momentum_reference_kg_m_s=momentum_ref,
        wake_momentum_increment_kg_m_s=wake_momentum,
    )


def canonical_json(obj: object) -> str:
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), allow_nan=False)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", default="data/les/godzilla_frigate_reduced_fixture.json")
    parser.add_argument("--max-relative-energy-residual", type=float, default=0.60)
    args = parser.parse_args()

    inp = Inputs()
    ledger = simulate(inp)

    # Sanity/admission checks for the toy itself. These do not validate the
    # physical adequacy of the reduced-order model.
    assert inp.dt_s > 0.0
    assert 0.0 <= inp.contact_restitution <= 1.0
    assert ledger.impact_impulse_N_s > 0.0
    assert ledger.contact_energy_J > 0.0
    assert ledger.water_drag_force_N >= 0.0
    assert ledger.air_drag_force_N >= 0.0
    assert ledger.residual_energy_relative <= args.max_relative_energy_residual

    core = {
        "schema": "les-godzilla-frigate-reduced-fixture-v1",
        "status": "reduced_order_regression_only",
        "stage_order": [
            "contact",
            "structure",
            "water",
            "air",
            "secondary_phase",
            "acoustics",
            "electromagnetism",
            "optical_observer",
        ],
        "inputs": asdict(inp),
        "ledger": asdict(ledger),
        "authority_boundaries": {
            "contact": "reduced 1-D impulse surrogate; not contact-FEA authority",
            "structure": "lumped dissipation fraction; not hull constitutive/failure authority",
            "water": "quadratic drag surrogate; not free-surface Navier-Stokes authority",
            "air": "quadratic drag surrogate; not atmospheric CFD authority",
            "secondary_phase": "energy bookkeeping only; not spray/foam multiphase authority",
            "acoustics": "energy bookkeeping only; not wave/acoustic-field authority",
            "electromagnetism": "bookkeeping channel only; not Maxwell field solution",
            "optics": "no image synthesis in this fixture",
        },
    }
    digest = hashlib.sha256(canonical_json(core).encode("utf-8")).hexdigest()
    artifact = {**core, "sha256_core": digest}

    path = Path(args.output)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(artifact, sort_keys=True, indent=2) + "\n", encoding="utf-8")
    print(path)
    print(digest)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
