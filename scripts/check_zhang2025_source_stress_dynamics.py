#!/usr/bin/env python3
"""Same-source, signed 1D dynamics + 3D vacuum EM-stress consumer for Zhang rigs.

This is a physically scoped *instrument-input compiler*, NOT a full Maxwell,
magnetisation, electromechanics, plasma, Einstein-matter or lab simulator.
Inputs are measured or explicitly synthetic time-aligned fields and geometry.
Missing background force bounds fail closed. Frames are NOT independent trials.
"""
from __future__ import annotations

import argparse
import json
import math
import re
from pathlib import Path

from check_zhang2025_em_gravity_bidi import (
    Interval, REQUIRED_FORCE_CLASSES, finite, force_interval,
    MU0 as MAGNETIC_PERMEABILITY,
)

EPS0 = 8.8541878128e-12
C = 299792458.0
DYNAMIC_BACKGROUND_CLASSES = tuple(
    c for c in REQUIRED_FORCE_CLASSES
    if c not in ("charge_force", "dielectrophoresis", "magnetic_gradient")
)
IDENTITY_FIELDS = (
    "apparatus_id", "source_class", "target_id", "axis",
    "protocol_id", "calibration_id", "instrument_id",
)
SOURCE_CLASSES = ("zhang2025_toroid", "zhang2025_HV_sphere")


def nonempty(data: dict, key: str) -> str:
    value = data.get(key)
    if not isinstance(value, str) or not value.strip():
        raise ValueError(f"{key}: nonempty string required")
    return value


def interval(value: dict, label: str) -> Interval:
    return force_interval(value, label)


def imul(left: Interval, right: Interval) -> Interval:
    corners = (
        left.lo * right.lo, left.lo * right.hi,
        left.hi * right.lo, left.hi * right.hi,
    )
    return Interval(min(corners), max(corners))


def iscale(value: Interval, coefficient: float) -> Interval:
    coefficient = finite(coefficient, "scale coefficient")
    return imul(value, Interval(coefficient, coefficient))


def idiv_positive(value: Interval, coefficient: float) -> Interval:
    coefficient = finite(coefficient, "positive denominator")
    if coefficient <= 0:
        raise ValueError("positive denominator required")
    return iscale(value, 1.0 / coefficient)


def vec3(value: object, label: str) -> tuple[float, float, float]:
    if not isinstance(value, list) or len(value) != 3:
        raise ValueError(f"{label}: require a measured 3-component vector")
    return tuple(finite(x, label) for x in value)


def vacuum_maxwell_stress(E_V_m: object, B_T: object) -> dict:
    """Lab-frame EM tensor for vacuum (no material magnetisation/pressure).

    Uses Maxwell traction sigma_ij =
      eps0 (E_i E_j - delta_ij E²/2)
      + (B_i B_j - delta_ij B²/2)/mu0,
    energy u = eps0 E²/2 + B²/(2mu0),
    Poynting S = E cross B/mu0.
    T^ij = -sigma_ij in this sign convention.
    """
    E = vec3(E_V_m, "E_V_m")
    B = vec3(B_T, "B_T")
    e2 = sum(x * x for x in E)
    b2 = sum(x * x for x in B)
    u = 0.5 * (EPS0 * e2 + b2 / MAGNETIC_PERMEABILITY)
    sigma = [
        [
            EPS0 * (E[i] * E[j] - (0.5 * e2 if i == j else 0.0))
            + (B[i] * B[j] - (0.5 * b2 if i == j else 0.0))
            / MAGNETIC_PERMEABILITY
            for j in range(3)
        ]
        for i in range(3)
    ]
    S = [
        (E[1] * B[2] - E[2] * B[1]) / MAGNETIC_PERMEABILITY,
        (E[2] * B[0] - E[0] * B[2]) / MAGNETIC_PERMEABILITY,
        (E[0] * B[1] - E[1] * B[0]) / MAGNETIC_PERMEABILITY,
    ]
    # -u + sum(T_ii) = -u - tr(sigma) = 0 for source-free Maxwell.
    lorentz_trace = -u - sum(sigma[i][i] for i in range(3))
    if not math.isclose(lorentz_trace, 0.0, abs_tol=1e-13 * max(1.0, u)):
        raise AssertionError("Maxwell tracelessness invariant violated")
    if any(not math.isclose(sigma[i][j], sigma[j][i], rel_tol=1e-12, abs_tol=1e-20)
           for i in range(3) for j in range(3)):
        raise AssertionError("Maxwell stress symmetry violated")
    flux_norm = math.sqrt(sum(x * x for x in S))
    if flux_norm > C * u * (1 + 1e-12):
        raise AssertionError("vacuum electromagnetic causal energy-flux bound violated")
    return {
        "energy_density_J_m3": u,
        "maxwell_traction_Pa": sigma,
        "energy_flux_W_m2": S,
        "lorentz_trace_Pa": lorentz_trace,
        "vacuum_stress_only": True,
        "material_stress_and_source_conservation_verified": False,
    }


def _timed_frame(frame: dict) -> None:
    finite(frame.get("t_s"), "time")
    interval(frame.get("x_m"), "position")
    vec3(frame.get("E_V_m"), "E_V_m")
    vec3(frame.get("B_T"), "B_T")
    interval(frame.get("grad_E2_x_V2_m3"), "grad E2")
    interval(frame.get("grad_B2_x_T2_m"), "grad B2")
    bg = frame.get("background_forces_N")
    if not isinstance(bg, dict):
        raise ValueError("background_forces_N must be a map of measured bounds")
    missing = sorted(set(DYNAMIC_BACKGROUND_CLASSES) - set(bg))
    if missing:
        raise ValueError("missing background class(es): " + ", ".join(missing))
    for key in DYNAMIC_BACKGROUND_CLASSES:
        interval(bg[key], key)


def validate_run(run: dict, mode: str) -> None:
    if run.get("source_mode") != mode:
        raise ValueError(f"expected source_mode {mode}")
    for key in (*IDENTITY_FIELDS, "run_id", "raw_data_sha256"):
        nonempty(run, key)
    if run["source_class"] not in SOURCE_CLASSES:
        raise ValueError("source_class must select one actual Zhang rig, not Pais")
    if not re.fullmatch(r"[0-9a-fA-F]{64}", run["raw_data_sha256"]):
        raise ValueError("raw_data_sha256: exact SHA-256 hex required (not independently verified)")
    if run.get("frame_times_calibrated") is not True:
        raise ValueError("frame_times_calibrated must be explicit")
    material = run.get("material")
    if not isinstance(material, dict):
        raise ValueError("material parameters required")
    for key in (
        "mass_kg", "electric_charge_C", "polarizability_C_m2_V",
        "magnetic_susceptibility", "sample_volume_m3",
        "spring_N_m", "damping_N_s_m", "equilibrium_x_m",
    ):
        interval(material.get(key), key)
    if material["mass_kg"]["nominal_N"] - material["mass_kg"]["bound_N"] <= 0:
        raise ValueError("strictly positive lower mass required")
    if material["sample_volume_m3"]["nominal_N"] - material["sample_volume_m3"]["bound_N"] <= 0:
        raise ValueError("strictly positive sample volume required")
    for key in ("spring_N_m", "damping_N_s_m"):
        if material[key]["nominal_N"] - material[key]["bound_N"] < 0:
            raise ValueError(f"{key}: negative physical lower coefficient")
    if run.get("quasistatic_linear_response_justified") is not True:
        raise ValueError("selected weak-response model applicability required")
    frames = run.get("frames")
    if not isinstance(frames, list) or len(frames) < 3:
        raise ValueError("at least three calibrated time frames required")
    for row in frames:
        _timed_frame(row)
    if any(b["t_s"] <= a["t_s"] for a, b in zip(frames, frames[1:])):
        raise ValueError("timestamps must strictly increase")


def _frame_force(run: dict, index: int) -> dict:
    f = run["frames"][index]
    previous = run["frames"][index - 1]
    following = run["frames"][index + 1]
    dt_prev = f["t_s"] - previous["t_s"]
    dt_next = following["t_s"] - f["t_s"]
    x_prev = interval(previous["x_m"], "previous x")
    x = interval(f["x_m"], "current x")
    x_next = interval(following["x_m"], "next x")
    velocity = idiv_positive(x_next - x_prev, dt_prev + dt_next)
    accel = iscale(
        idiv_positive(
            idiv_positive(x_next - x, dt_next)
            - idiv_positive(x - x_prev, dt_prev),
            dt_prev + dt_next,
        ), 2.0,
    )
    m = run["material"]
    mass = interval(m["mass_kg"], "mass")
    damping = interval(m["damping_N_s_m"], "damping")
    spring = interval(m["spring_N_m"], "spring")
    equilibrium = interval(m["equilibrium_x_m"], "equilibrium")
    # Dynamics: F_external = m*a + damping*v + k*(x-x0).
    inferred_external = (
        imul(mass, accel)
        + imul(damping, velocity)
        + imul(spring, x - equilibrium)
    )
    charge = interval(m["electric_charge_C"], "charge")
    polarizability = interval(m["polarizability_C_m2_V"], "polarizability")
    chi = interval(m["magnetic_susceptibility"], "susceptibility")
    volume = interval(m["sample_volume_m3"], "volume")
    efield = Interval(f["E_V_m"][0], f["E_V_m"][0])
    classical = (
        imul(charge, efield)
        + iscale(imul(polarizability,
                     interval(f["grad_E2_x_V2_m3"], "gradE2")), 0.5)
        + iscale(imul(imul(chi, volume),
                     interval(f["grad_B2_x_T2_m"], "gradB2")),
                 1.0 / (2 * MAGNETIC_PERMEABILITY))
    )
    for key in DYNAMIC_BACKGROUND_CLASSES:
        classical = classical + interval(f["background_forces_N"][key], key)
    residual = inferred_external - classical
    return {
        "t_s": f["t_s"],
        "velocity_m_s": [velocity.lo, velocity.hi],
        "acceleration_m_s2": [accel.lo, accel.hi],
        "external_force_dynamics_N": [inferred_external.lo, inferred_external.hi],
        "ordinary_force_N": [classical.lo, classical.hi],
        "signed_force_residual_N": [residual.lo, residual.hi],
        "residual_excludes_zero": residual.lo > 0 or residual.hi < 0,
        "vacuum_EM": vacuum_maxwell_stress(f["E_V_m"], f["B_T"]),
    }


def evaluate_pair(payload: dict) -> dict:
    """Paired trajectories give correlated force residuals; never a CI by frames."""
    if payload.get("data_kind") not in ("synthetic", "real_unverified"):
        raise ValueError("data_kind must be synthetic or real_unverified")
    on, off = payload.get("on"), payload.get("off")
    if not isinstance(on, dict) or not isinstance(off, dict):
        raise ValueError("both ON and OFF source records required")
    validate_run(on, "ON")
    validate_run(off, "OFF")
    for key in IDENTITY_FIELDS:
        if on[key] != off[key]:
            raise ValueError(f"same-object mismatch: {key}")
    if on["material"] != off["material"]:
        raise ValueError("same-object mismatch: material/source parameters")
    if on["run_id"] == off["run_id"] or on["raw_data_sha256"] == off["raw_data_sha256"]:
        raise ValueError("ON/OFF must have distinct run IDs and data hashes")
    if len(on["frames"]) != len(off["frames"]):
        raise ValueError("ON/OFF frame counts do not match")
    if any(a["t_s"] != b["t_s"] for a, b in zip(on["frames"], off["frames"])):
        raise ValueError("ON/OFF timestamps are not pair-aligned")
    paired_rows = []
    for idx in range(1, len(on["frames"]) - 1):
        on_result, off_result = _frame_force(on, idx), _frame_force(off, idx)
        on_interval = Interval(*on_result["signed_force_residual_N"])
        off_interval = Interval(*off_result["signed_force_residual_N"])
        difference = on_interval - off_interval
        paired_rows.append({
            "t_s": on_result["t_s"],
            "on": on_result,
            "off": off_result,
            "paired_residual_N": [difference.lo, difference.hi],
            "zero_excluded": difference.lo > 0 or difference.hi < 0,
        })
    return {
        "data_kind": payload["data_kind"],
        "apparatus_id": on["apparatus_id"],
        "source_class": on["source_class"],
        "paired_frames": paired_rows,
        "confidence_interval_95": None,
        "all_frames_are_independent_replicates": False,
        "material_stress_conservation_verified": False,
        "source_to_metric_solution_verified": False,
        "ordinary_model_is_complete": False,
        "gravity_anomaly_established": False,
        "summary": (
            "A bounded, conditional 1D force/position residual and vacuum EM stress "
            "have been computed; constitutive memory, source-current Maxwell "
            "equations, material/elastic stress, conserved total stress, nuisance "
            "validation and independent tests remain distinct source payments. "
            "Individual frames are autocorrelated, not statistical replications."
        ),
    }


def main() -> None:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--input", type=Path, required=True)
    args = p.parse_args()
    print(json.dumps(evaluate_pair(
        json.loads(args.input.read_text(encoding="utf-8"))
    ), sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
