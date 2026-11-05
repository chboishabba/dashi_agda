#!/usr/bin/env python3
"""Source-bounded Zhang 2025 pulsed-EM gravity-like motion audit.

This is a one-dimensional, signed-force *interval comparator*, not a gravity
detector. Missing controls remain missing. Synthetic examples never become
empirical receipts. The selected weak/static formulae below do not constitute
a complete high-voltage pulsed-field model or a dynamic field solution.
"""
from __future__ import annotations

import argparse
import json
import math
import re
from dataclasses import dataclass
from pathlib import Path

MU0 = 1.25663706127e-6  # N / A^2, approximate SI constant
C = 299792458.0         # m / s, exact SI
PATENT_US = "US12417870B1"
PATENT_CN = "CN119943525A"

# An investigator must supply bounded results, not ungrounded zero defaults.
REQUIRED_FORCE_CLASSES = (
    "charge_force",
    "dielectrophoresis",
    "magnetic_gradient",
    "time_varying_induction",
    "suspension_and_support",
    "mechanical_vibration",
    "thermal_drift",
    "residual_gas_and_ionic_wind",
    "rf_instrumentation",
    "radiative_momentum",
    "unmodelled_cross_couplings",
)


def finite(value: object, name: str) -> float:
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        raise ValueError(f"{name}: finite number required")
    x = float(value)
    if not math.isfinite(x):
        raise ValueError(f"{name}: nonfinite value")
    return x


def linear_electric_force(charge_C: float, electric_field_V_m: float) -> float:
    """qE in the selected direction; E is local signed field, not V/gap."""
    return finite(charge_C, "charge_C") * finite(electric_field_V_m, "E")


def linear_dielectrophoresis(alpha_C_m2_V: float, grad_e2_V2_m3: float) -> float:
    """0.5 alpha grad(E^2), quasistatic, weak, isotropic polarizability."""
    return 0.5 * finite(alpha_C_m2_V, "alpha") * finite(grad_e2_V2_m3, "gradE2")


def linear_magnetic_gradient(
    chi_dimensionless: float, volume_m3: float, grad_b2_T2_m: float
) -> float:
    """chi*volume*grad(B^2)/(2 mu0), linear isotropic weak-response case."""
    return (
        finite(chi_dimensionless, "chi")
        * finite(volume_m3, "volume")
        * finite(grad_b2_T2_m, "gradB2")
        / (2 * MU0)
    )


def nominal_input_power(voltage_V: float, current_A: float) -> float:
    """Nominal VI only: excludes pulsed waveform, reactive and stored energy."""
    return finite(voltage_V, "voltage") * finite(current_A, "current")


@dataclass(frozen=True)
class Interval:
    lo: float
    hi: float

    def __post_init__(self) -> None:
        if not math.isfinite(self.lo) or not math.isfinite(self.hi) or self.lo > self.hi:
            raise ValueError("invalid finite interval")

    def __add__(self, other: "Interval") -> "Interval":
        return Interval(self.lo + other.lo, self.hi + other.hi)

    def __sub__(self, other: "Interval") -> "Interval":
        return Interval(self.lo - other.hi, self.hi - other.lo)

    def overlaps(self, other: "Interval") -> bool:
        return self.lo <= other.hi and other.lo <= self.hi

    def as_dict(self) -> dict[str, float]:
        return {"lo_N": self.lo, "hi_N": self.hi}


def force_interval(value: dict, field: str) -> Interval:
    if not isinstance(value, dict):
        raise ValueError(f"{field}: object expected")
    x = finite(value.get("nominal_N"), f"{field}.nominal_N")
    u = finite(value.get("bound_N"), f"{field}.bound_N")
    if u < 0:
        raise ValueError(f"{field}: negative uncertainty")
    receipt = value.get("evidence_receipt")
    if not isinstance(receipt, str) or not receipt.strip():
        raise ValueError(f"{field}: explicit evidence_receipt required")
    return Interval(x - u, x + u)


def _id(obj: dict, name: str) -> str:
    x = obj.get(name)
    if not isinstance(x, str) or not x.strip():
        raise ValueError(f"{name}: nonempty string required")
    return x


def validate_run(run: dict, expected_mode: str) -> None:
    if not isinstance(run, dict):
        raise ValueError("ON/OFF run must be an object")
    if run.get("source_mode") != expected_mode:
        raise ValueError(f"expected source_mode {expected_mode}")
    for field in (
        "apparatus_id", "target_id", "force_axis", "configuration_id",
        "calibration_id", "instrument_id", "run_id", "raw_data_sha256",
    ):
        _id(run, field)
    if not re.fullmatch(r"[a-fA-F0-9]{64}", run["raw_data_sha256"]):
        raise ValueError("raw_data_sha256 must be a 64-character hex digest")
    if run.get("channel") != "signed_force_N":
        raise ValueError(
            "channel must be signed_force_N; a rotating ball is not a "
            "calibrated force reading"
        )
    force_interval(run.get("measurement"), "measurement")
    if not isinstance(run.get("force_classes"), dict):
        raise ValueError("force_classes must be an object")


def evaluate(payload: dict) -> dict:
    """Fail closed: a disjoint interval is a candidate residual, not gravity."""
    if not isinstance(payload, dict):
        raise ValueError("object payload expected")
    if payload.get("patent_reference") not in (PATENT_US, PATENT_CN):
        raise ValueError("pin an original Zhang patent-family reference")
    kind = payload.get("data_kind")
    if kind not in ("real_unverified", "synthetic"):
        raise ValueError("data_kind must be real_unverified or synthetic")
    on = payload["on"]
    off = payload["off"]
    validate_run(on, "ON")
    validate_run(off, "OFF")
    for field in (
        "apparatus_id", "target_id", "force_axis", "configuration_id",
        "calibration_id", "instrument_id",
    ):
        if on[field] != off[field]:
            raise ValueError(f"ON/OFF same-object mismatch: {field}")
    if on["run_id"] == off["run_id"]:
        raise ValueError("ON/OFF must be distinct runs")

    missing = sorted(
        set(REQUIRED_FORCE_CLASSES)
        - (set(on["force_classes"]) & set(off["force_classes"]))
    )
    base = {
        "patent_reference": payload["patent_reference"],
        "data_kind": kind,
        "apparatus_id": on["apparatus_id"],
        "channel": on["channel"],
        "gravity_identified": False,
        "independent_replication_established": False,
        "metric_or_TT_strain_established": False,
    }
    if missing:
        return {
            **base,
            "status": "incomplete_ordinary_force_comparator",
            "missing_force_classes": missing,
            "note": "No omitted force class is assigned a zero bound.",
        }

    zero = Interval(0.0, 0.0)
    predicted_on = zero
    predicted_off = zero
    for label in REQUIRED_FORCE_CLASSES:
        predicted_on = predicted_on + force_interval(on["force_classes"][label], "ON." + label)
        predicted_off = predicted_off + force_interval(off["force_classes"][label], "OFF." + label)

    measured_change = force_interval(on["measurement"], "ON.measurement") - (
        force_interval(off["measurement"], "OFF.measurement")
    )
    predicted_change = predicted_on - predicted_off
    residual = measured_change - predicted_change
    if kind == "synthetic":
        status = "synthetic_fixture_only"
    elif residual.lo <= 0 <= residual.hi:
        status = "ordinary_force_interval_compatible"
    else:
        status = "candidate_unexplained_signed_force_residual"
    return {
        **base,
        "status": status,
        "missing_force_classes": [],
        "measured_on_minus_off_N": measured_change.as_dict(),
        "classical_on_minus_off_N": predicted_change.as_dict(),
        "unexplained_signed_force_N": residual.as_dict(),
        "nonzero_residual_interval": (residual.lo > 0 or residual.hi < 0),
        "note": (
            "A nonzero bound can justify source-specific follow-up only; "
            "receipts and model adequacy are not authenticated by this script. "
            "Anomaly != metric, negative-G, unique mechanism or GW."
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, help="ON/OFF JSON case; no implicit sample data")
    args = parser.parse_args()
    if args.input is None:
        parser.print_help()
        return
    payload = json.loads(args.input.read_text(encoding="utf-8"))
    print(json.dumps(evaluate(payload), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
