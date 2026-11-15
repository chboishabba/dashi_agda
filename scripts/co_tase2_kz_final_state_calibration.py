"""Free-electron final-state k_z calibration consumer for Co1/4TaSe2 ARPES.

This does not infer missing calibration parameters.  It consumes explicitly
supplied work function, inner potential, emission angle, binding energy and c
lattice constant, then computes absolute and reciprocal-lattice-folded k_z.

Formula:
  E_kin = hnu - work_function - binding_energy
  k_z = sqrt((E_kin cos^2(theta) + V0) / (hbar^2/2m_e))
with hbar^2/(2m_e)=3.80998211615486 eV Angstrom^2.

The free-electron final-state approximation is a calibration model, not an
exact many-body theorem.  A literal Co1/4TaSe2 observer still needs same-object
raw-wave axes and calibration parameters/uncertainties.
"""
from __future__ import annotations

import argparse
import json
import math
from pathlib import Path

HBAR2_OVER_2ME_EV_A2 = 3.80998211615486


def kz_inverse_a(photon_energy_ev, work_function_ev, binding_energy_ev,
                 theta_deg, inner_potential_ev):
    e_kin = photon_energy_ev - work_function_ev - binding_energy_ev
    if e_kin <= 0:
        raise ValueError("photoelectron kinetic energy must be positive")
    inside = e_kin * math.cos(math.radians(theta_deg)) ** 2 + inner_potential_ev
    if inside <= 0:
        raise ValueError("final-state square-root argument must be positive")
    return math.sqrt(inside / HBAR2_OVER_2ME_EV_A2)


def fold_to_first_period(kz, c_angstrom):
    if c_angstrom <= 0:
        raise ValueError("c_angstrom must be positive")
    g = 2.0 * math.pi / c_angstrom
    # [0,G) folding; callers comparing a symmetry plane should compare modulo G.
    return kz % g, g


def evaluate(config_path, receipt_path=None):
    p = Path(config_path)
    d = json.loads(p.read_text())
    required = (
        "work_function_ev", "inner_potential_ev", "c_angstrom",
        "calibration_model", "parameter_source", "points",
    )
    missing = [k for k in required if k not in d]
    if missing:
        raise ValueError(f"missing calibration fields: {missing}")
    model = str(d["calibration_model"]).strip()
    source = str(d["parameter_source"]).strip()
    if not model or not source:
        raise ValueError("calibration_model and parameter_source must be declared")
    phi = float(d["work_function_ev"])
    v0 = float(d["inner_potential_ev"])
    c = float(d["c_angstrom"])
    if not all(math.isfinite(x) for x in (phi, v0, c)) or c <= 0:
        raise ValueError("invalid calibration parameters")
    points = d["points"]
    if not isinstance(points, list) or len(points) < 1:
        raise ValueError("points must be a non-empty list")

    out_points = []
    for row in points:
        hv = float(row["photon_energy_ev"])
        eb = float(row.get("binding_energy_ev", 0.0))
        theta = float(row.get("theta_deg", 0.0))
        kz = kz_inverse_a(hv, phi, eb, theta, v0)
        folded, reciprocal_period = fold_to_first_period(kz, c)
        out = {
            "label": str(row.get("label", "")),
            "photon_energy_ev": hv,
            "binding_energy_ev": eb,
            "theta_deg": theta,
            "kz_absolute_inv_a": kz,
            "reciprocal_period_inv_a": reciprocal_period,
            "kz_folded_inv_a": folded,
            "kz_folded_fraction_of_2pi_over_c": folded / reciprocal_period,
        }
        if "published_kz_fraction_of_2pi_over_c" in row:
            target = float(row["published_kz_fraction_of_2pi_over_c"]) % 1.0
            # Circular distance on the reciprocal period.
            delta = abs((out["kz_folded_fraction_of_2pi_over_c"] - target + 0.5) % 1.0 - 0.5)
            out["published_target_fraction"] = target
            out["folded_fraction_circular_residual"] = delta
        out_points.append(out)

    receipt = {
        "model": model,
        "parameter_source": source,
        "work_function_ev": phi,
        "inner_potential_ev": v0,
        "c_angstrom": c,
        "points": out_points,
        "epistemic_boundary": (
            "free-electron final-state calibration conditional on supplied parameters; "
            "does not infer Co1/4TaSe2 V0/work function or replace raw ARPES axis metadata"
        ),
    }
    if receipt_path:
        Path(receipt_path).write_text(json.dumps(receipt, indent=2) + "\n")
    return receipt


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("config_json")
    parser.add_argument("--receipt")
    args = parser.parse_args()
    print(json.dumps(evaluate(args.config_json, args.receipt), indent=2))
