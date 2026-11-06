#!/usr/bin/env python3
"""Bounded rotation/torsion comparison for the patent suspended-ball consumer.

A separate rotational experiment is not a translational force, free-fall,
metric, or TT-strain detector. No experiment is supplied by this module.
A conservative interval covers angle and constitutive uncertainty; dynamic
frames are not independent statistical trials.
"""
from __future__ import annotations

import argparse
import json
import math
from pathlib import Path

from check_zhang2025_source_stress_dynamics import (
    MAGNETIC_PERMEABILITY, SOURCE_CLASSES, IDENTITY_FIELDS,
    Interval, finite, interval, vec3, imul, iscale,
    idiv_interval_positive, time_interval, nonempty, vacuum_maxwell_stress,
)

TORQUE_BACKGROUND_CLASSES = (
    "thread_asymmetry",
    "air_and_ionic_wind",
    "vibration_and_mounts",
    "thermal_transients",
    "magnetic_hysteresis_and_eddy",
    "charge_loss_and_leakage",
    "rf_pickup",
    "unmodelled_torque",
)


def sine_interval(argument: Interval) -> Interval:
    """Exact min/max of sin on a finite real interval, critical points included."""
    if argument.hi - argument.lo >= 2 * math.pi:
        return Interval(-1., 1.)
    endpoints = [math.sin(argument.lo), math.sin(argument.hi)]
    k0 = math.ceil((argument.lo - math.pi / 2) / math.pi)
    k1 = math.floor((argument.hi - math.pi / 2) / math.pi)
    for k in range(k0, k1 + 1):
        endpoints.append(1. if k % 2 == 0 else -1.)
    return Interval(min(endpoints), max(endpoints))


def _validate_frame(f: dict) -> None:
    time_interval(f)
    for key in (
        "theta_rad", "E2_V2_m2", "B2_T2", "electric_axis_angle_rad",
        "magnetic_axis_angle_rad",
    ):
        interval(f.get(key), key)
    E = vec3(f.get("E_V_m"), "E_V_m")
    B = vec3(f.get("B_T"), "B_T")
    e2 = interval(f["E2_V2_m2"], "E2")
    b2 = interval(f["B2_T2"], "B2")
    if e2.lo < 0 or b2.lo < 0:
        raise ValueError("squared field magnitude must be nonnegative")
    en = sum(x*x for x in E)
    bn = sum(x*x for x in B)
    if not e2.lo <= en <= e2.hi or not b2.lo <= bn <= b2.hi:
        raise ValueError("measured vector field outside stated E2/B2 interval")
    # Planar torsion: instrument-reported field axes must agree with measured
    # x/y field vectors (mod pi, since the torque depends on E² and B²).
    for vector, scalar, key in (
        (E, en, "electric_axis_angle_rad"),
        (B, bn, "magnetic_axis_angle_rad"),
    ):
        if abs(vector[2]) > 1e-12 * max(math.sqrt(scalar), 1e-30):
            raise ValueError("selected planar torsion requires negligible z field")
        if scalar > 0:
            measured_axis = interval(f[key], key)
            theta_axis = (measured_axis.lo + measured_axis.hi) / 2
            phase_delta = math.remainder(
                theta_axis - math.atan2(vector[1], vector[0]), math.pi
            )
            axis_uncertainty = (measured_axis.hi - measured_axis.lo) / 2
            if abs(phase_delta) > axis_uncertainty + 1e-10:
                raise ValueError("field-axis angle disagrees with vector E/B")
    backgrounds = f.get("background_torques_Nm")
    if not isinstance(backgrounds, dict):
        raise ValueError("bounded background torque map required")
    missing = sorted(set(TORQUE_BACKGROUND_CLASSES) - set(backgrounds))
    if missing:
        raise ValueError("missing torque backgrounds: " + ", ".join(missing))
    for key in TORQUE_BACKGROUND_CLASSES:
        interval(backgrounds[key], key)


def validate_torsion_run(run: dict, mode: str) -> None:
    if run.get("source_mode") != mode:
        raise ValueError(f"expected {mode} source")
    for key in (*IDENTITY_FIELDS, "run_id", "raw_data_sha256"):
        nonempty(run, key)
    if run["source_class"] not in SOURCE_CLASSES:
        raise ValueError("choose the selected real-world Zhang source class")
    if len(run["raw_data_sha256"]) != 64 or any(
        c not in "0123456789abcdefABCDEF" for c in run["raw_data_sha256"]
    ):
        raise ValueError("source SHA-256 required")
    if run.get("frame_times_calibrated") is not True:
        raise ValueError("calibrated timestamps required")
    if run.get("linear_quasistatic_anisotropy_justified") is not True:
        raise ValueError("linear/quasistatic anisotropy assumption not declared")
    material = run.get("material")
    if not isinstance(material, dict):
        raise ValueError("torsion material+thread data required")
    for key in (
        "inertia_kg_m2", "damping_Nm_s_rad", "torsion_Nm_rad",
        "zero_angle_rad", "electric_polarizability_anisotropy_C_m2_V",
        "magnetic_susceptibility_anisotropy", "sample_volume_m3",
    ):
        interval(material.get(key), key)
    for key in ("inertia_kg_m2", "sample_volume_m3"):
        if interval(material[key], key).lo <= 0:
            raise ValueError(f"{key} must be strictly positive")
    for key in ("damping_Nm_s_rad", "torsion_Nm_rad"):
        if interval(material[key], key).lo < 0:
            raise ValueError(f"{key} must be nonnegative")
    frames = run.get("frames")
    if not isinstance(frames, list) or len(frames) < 3:
        raise ValueError("three or more frames required")
    for f in frames:
        _validate_frame(f)
    if any(time_interval(b).lo <= time_interval(a).hi
           for a, b in zip(frames, frames[1:])):
        raise ValueError("strictly non-overlapping calibrated timestamp intervals required")


def _torque_model(run: dict, i: int) -> dict:
    frames = run["frames"]
    past, current, future = frames[i-1:i+2]
    t_prev, t_curr, t_next = (
        time_interval(past), time_interval(current), time_interval(future)
    )
    dt1 = t_curr - t_prev
    dt2 = t_next - t_curr
    p = interval(past["theta_rad"], "theta prev")
    th = interval(current["theta_rad"], "theta")
    n = interval(future["theta_rad"], "theta next")
    omega = idiv_interval_positive(n - p, t_next - t_prev)
    angular_accel = iscale(
        idiv_interval_positive(
            idiv_interval_positive(n - th, dt2) -
            idiv_interval_positive(th - p, dt1), dt1 + dt2
        ), 2.,
    )
    m = run["material"]
    inertia = interval(m["inertia_kg_m2"], "inertia")
    damp = interval(m["damping_Nm_s_rad"], "damping")
    spring = interval(m["torsion_Nm_rad"], "torsion")
    rest = interval(m["zero_angle_rad"], "zero")
    inferred = (
        imul(inertia, angular_accel)
        + imul(damp, omega)
        + imul(spring, th - rest)
    )
    field_e_axis = interval(current["electric_axis_angle_rad"], "electric angle")
    field_b_axis = interval(current["magnetic_axis_angle_rad"], "magnetic angle")
    e_sine = sine_interval(iscale(field_e_axis - th, 2.))
    b_sine = sine_interval(iscale(field_b_axis - th, 2.))
    electric_torque = iscale(
        imul(imul(
            interval(m["electric_polarizability_anisotropy_C_m2_V"], "alpha delta"),
            interval(current["E2_V2_m2"], "E2"),
        ), e_sine), 0.5
    )
    magnetic_torque = iscale(
        imul(imul(
            imul(
                interval(m["magnetic_susceptibility_anisotropy"], "chi delta"),
                interval(m["sample_volume_m3"], "volume"),
            ),
            interval(current["B2_T2"], "B2"),
        ), b_sine), 1.0 / (2 * MAGNETIC_PERMEABILITY)
    )
    conventional = electric_torque + magnetic_torque
    for key in TORQUE_BACKGROUND_CLASSES:
        conventional += interval(current["background_torques_Nm"][key], key)
    residual = inferred - conventional
    return {
        "t_s": current["t_s"],
        "angular_velocity_rad_s": [omega.lo, omega.hi],
        "angular_acceleration_rad_s2": [angular_accel.lo, angular_accel.hi],
        "inferred_external_torque_Nm": [inferred.lo, inferred.hi],
        "ordinary_torque_Nm": [conventional.lo, conventional.hi],
        "unexplained_torque_Nm": [residual.lo, residual.hi],
        "vacuum_EM": vacuum_maxwell_stress(current["E_V_m"], current["B_T"]),
    }


def evaluate_pair(payload: dict) -> dict:
    if payload.get("data_kind") not in ("synthetic", "real_unverified"):
        raise ValueError("data_kind must be synthetic or real_unverified")
    on, off = payload.get("on"), payload.get("off")
    if not isinstance(on, dict) or not isinstance(off, dict):
        raise ValueError("ON/OFF torsion records required")
    validate_torsion_run(on, "ON")
    validate_torsion_run(off, "OFF")
    for k in IDENTITY_FIELDS:
        if on[k] != off[k]:
            raise ValueError(f"same-object torsion mismatch: {k}")
    if on["material"] != off["material"]:
        raise ValueError("same-object torsion mismatch: material")
    if on["run_id"] == off["run_id"] or on["raw_data_sha256"] == off["raw_data_sha256"]:
        raise ValueError("torsion runs require distinct IDs and raw data hashes")
    if len(on["frames"]) != len(off["frames"]) or any(
        a["t_s"] != b["t_s"] for a, b in zip(on["frames"], off["frames"])
    ):
        raise ValueError("torsion time grids must align")
    rows = []
    for i in range(1, len(on["frames"])-1):
        a, b = _torque_model(on, i), _torque_model(off, i)
        delta = Interval(*a["unexplained_torque_Nm"]) - Interval(*b["unexplained_torque_Nm"])
        rows.append({
            "t_s": a["t_s"], "on": a, "off": b,
            "paired_signed_torque_residual_Nm": [delta.lo, delta.hi],
            "zero_excluded": delta.lo > 0 or delta.hi < 0,
        })
    return {
        "apparatus_id": on["apparatus_id"],
        "source_class": on["source_class"],
        "consumer": "rotation_or_thread_torsion_not_weight_or_spacetime",
        "data_kind": payload["data_kind"],
        "paired_frames": rows,
        "confidence_interval_95": None,
        "frames_are_independent_replicates": False,
        "full_material_and_apparatus_torque_model_complete": False,
        "metric_perturbation_measured": False,
        "gravity_anomaly_established": False,
        "note": (
            "Anisotropic dipole and torsion are only selected classical terms. "
            "Lossy dielectric phase-lag, unmeasured charge, eddy currents, "
            "support nonlinearity and RF vibration require actual bounded controls."
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, required=True)
    args = parser.parse_args()
    case = json.loads(args.input.read_text(encoding="utf-8"))
    print(json.dumps(evaluate_pair(case), sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
