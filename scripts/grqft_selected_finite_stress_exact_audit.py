#!/usr/bin/env python3
"""Independent exact-rational reproduction of a selected finite-measure stress receipt.

This evaluator deliberately cannot certify a CMP119 published-action match,
renormalized T_mu_nu, or a cosmological/antigravity prediction. It computes the
same selected Haar/density/insertion for every slot and reports the raw A,B,D,Z,
C=B*Z-A*D and the separate timelike, spatial and trace contractions.

Input requires one immutable source identity/cutoff/metric frame and explicit
per-configuration, per-slot action/insertion variations. Metadata alone is NOT
authority. The Gibbs logarithmic derivative d(rho)=-rho*dS and metric-independent
Haar weight are mathematical assumptions to validate independently.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import sys

SLOTS = ("00", "01", "02", "03", "11", "12", "13", "22", "23", "33")
DIAGONAL = ("00", "11", "22", "33")


def q(value: object) -> Fraction:
    if isinstance(value, bool) or not isinstance(value, (str, int)):
        raise ValueError(f"Expected an exact fraction string/integer, got {value!r}")
    return Fraction(value)


def fmt(value: Fraction) -> str:
    return str(value)


def validate_text(obj: dict, key: str) -> str:
    value = obj.get(key)
    if not isinstance(value, str) or not value.strip():
        raise ValueError(f"Missing nonempty {key} identity")
    return value


def audit(source: dict) -> dict:
    provenance = source.get("provenance")
    if not isinstance(provenance, dict):
        raise ValueError("Missing provenance object")
    for key in ("source_identifier", "revision", "selected_action",
                "measure_identifier", "cutoff", "metric_frame",
                "observable_identifier", "normalization"):
        validate_text(provenance, key)
    if provenance.get("haar_metric_independent") is not True:
        raise ValueError("Metric independence of Haar must be explicitly declared")
    if provenance.get("gibbs_logarithmic_derivative") != "d_rho=-rho*dS":
        raise ValueError("Gibbs derivative convention is unselected")
    if source.get("slots") != list(SLOTS):
        raise ValueError("Missing/corrupt symmetric tensor slot order")
    configs = source.get("configurations")
    if not isinstance(configs, list) or not configs:
        raise ValueError("Need a nonempty explicit finite configuration family")
    if len(configs) != len(set(c.get("id") for c in configs)):
        raise ValueError("Configuration IDs are not unique")

    A = Fraction(0)
    Z = Fraction(0)
    B = {slot: Fraction(0) for slot in SLOTS}
    D = {slot: Fraction(0) for slot in SLOTS}
    trace_insertion = Fraction(0)
    trace_action_violations = []
    rows = []
    for c in configs:
        if not isinstance(c, dict):
            raise ValueError("Configuration must be an object")
        key = validate_text(c, "id")
        w, rho, o = (q(c[field]) for field in ("haar_weight", "density", "insertion"))
        if w < 0 or rho < 0:
            raise ValueError(f"Negative Haar/density in {key}")
        ds, do = c.get("d_action"), c.get("d_insertion")
        if not isinstance(ds, dict) or not isinstance(do, dict):
            raise ValueError(f"Missing metric derivatives in {key}")
        if set(ds) != set(SLOTS) or set(do) != set(SLOTS):
            raise ValueError(f"Not all ten canonical slots are present in {key}")
        dsq = {slot: q(ds[slot]) for slot in SLOTS}
        doq = {slot: q(do[slot]) for slot in SLOTS}
        action_trace = sum((dsq[slot] for slot in DIAGONAL), Fraction(0))
        insertion_trace = sum((doq[slot] for slot in DIAGONAL), Fraction(0))
        if action_trace:
            trace_action_violations.append(key)
        Z += w * rho
        A += w * rho * o
        trace_insertion += w * rho * insertion_trace
        for slot in SLOTS:
            d_rho = -rho * dsq[slot]
            D[slot] += w * d_rho
            B[slot] += w * (d_rho * o + rho * doq[slot])
        rows.append({"configuration": key,
                     "action_diagonal_trace": fmt(action_trace),
                     "insertion_diagonal_trace": fmt(insertion_trace)})
    if Z <= 0:
        raise ValueError("Selected partition Z is not strictly positive")
    if trace_action_violations:
        raise ValueError(f"Classical d=4 Wilson action trace fails at {trace_action_violations}")

    C = {slot: B[slot] * Z - A * D[slot] for slot in SLOTS}
    trace = sum((C[slot] for slot in DIAGONAL), Fraction(0))
    qtrace_rhs = Z * trace_insertion
    if trace != qtrace_rhs:
        raise ArithmeticError("Independent four-diagonal Gibbs identity failed")
    time_value = C["00"]
    spatial = sum((C[slot] for slot in ("11", "22", "33")), Fraction(0))
    # Only in a selected orthonormal Lorentzian frame when the numerical
    # C values have been independently identified with its T components.
    active = time_value + spatial
    # Lorentzian trace (-+++) in the same frame is -T00+spatial.
    lorentzian_trace = -time_value + spatial
    if active != lorentzian_trace + 2 * time_value:
        raise ArithmeticError("Lorentzian active/trace identity failed")

    result = {
        "status": "finite_rational_numerical_reproduction_only",
        "physical_source_identification_proved": False,
        "metric_variation_of_selected_action_proved": False,
        "renormalized_continuum_stress_proved": False,
        "gravitational_backreaction_proved": False,
        "provenance": provenance,
        "n_configurations": len(configs),
        "Z": fmt(Z),
        "A": fmt(A),
        "B": {slot: fmt(B[slot]) for slot in SLOTS},
        "D": {slot: fmt(D[slot]) for slot in SLOTS},
        "connected_cross_numerator": {slot: fmt(C[slot]) for slot in SLOTS},
        "connected_normalized_derivative": {
            slot: fmt(C[slot] / (Z * Z)) for slot in SLOTS},
        "four_diagonal_sum": fmt(trace),
        "gibbs_trace_insertion": fmt(trace_insertion),
        "trace_identity_rhs": fmt(qtrace_rhs),
        "timelike_component": fmt(time_value),
        "spatial_component_sum": fmt(spatial),
        "lorentzian_trace_candidate": fmt(lorentzian_trace),
        "lorentzian_active_candidate": fmt(active),
        "weak_coupling_nonnegative_active_compatible":
            active >= 0,
        "per_configuration": rows,
        "warning": "The Lorentzian components are candidates only; no Euclidean-to-Lorentzian same-source theorem, SI calibration, or continuum tensor has been provided."
    }

    geometry = source.get("geometry_diagnostic")
    if geometry is not None:
        if not isinstance(geometry, dict):
            raise ValueError("geometry_diagnostic must be an object")
        if validate_text(geometry, "metric_frame") != provenance["metric_frame"]:
            raise ValueError("Geometry comparison uses a different metric frame")
        validate_text(geometry, "geometry_revision")
        validate_text(geometry, "source_to_geometry_normalization")
        predicted = geometry.get("einstein_tensor")
        if not isinstance(predicted, dict) or set(predicted) != set(SLOTS):
            raise ValueError("Geometry must supply all ten exact Einstein tensor components")
        factor = q(geometry["source_to_geometry_normalization"])
        residual = {slot: q(predicted[slot]) -
                    factor * C[slot] / (Z * Z) for slot in SLOTS}
        result["geometry_diagnostic"] = {
            "status": "same_frame_exact_rational_residual_only",
            "physical_same_object_identification_proved": False,
            "source_normalization_factor": fmt(factor),
            "geometry_revision": geometry["geometry_revision"],
            "ten_slot_residual": {slot: fmt(residual[slot]) for slot in SLOTS},
            "all_ten_residuals_zero": all(value == 0 for value in residual.values()),
            "warning": "A zero numerical tensor residual cannot establish source identity, real analytic continuation, or a continuum Einstein solution."
        }

    return result


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("receipt", type=Path, help="selected JSON finite measure/derivative receipt")
    parser.add_argument("--out", type=Path, default=None)
    args = parser.parse_args()
    try:
        raw_bytes = args.receipt.read_bytes()
        receipt = json.loads(raw_bytes)
        report = audit(receipt)
        report["input_sha256"] = hashlib.sha256(raw_bytes).hexdigest()
        rendered = json.dumps(report, sort_keys=True, indent=2) + "\n"
        if args.out:
            args.out.write_text(rendered)
        else:
            print(rendered, end="")
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError) as error:
        print(f"FAIL-CLOSED: {error}", file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
