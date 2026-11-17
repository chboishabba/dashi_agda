#!/usr/bin/env python3
"""Exact-Fraction, fail-closed original synchronized V/I work interval reader.

Numerical bounds are conditional on supplied calibration error intervals,
sample synchronisation and integration assumptions. This DOES NOT prove the
errors, original device identity, Maxwell flux, natural-source independence,
storage restoration, or atmospheric causality. Never mark F10/F15 CLOSED.
"""
from __future__ import annotations

import argparse
import csv
from fractions import Fraction
import hashlib
import json
from pathlib import Path
from typing import Any

PORTS = ("natural_incident", "natural_outgoing", "controller_incident",
         "controller_outgoing", "load_output")
FIELDS = ("time_s", "voltage_V", "current_A", "voltage_error_V", "current_error_A")
REQUIRED_MANIFEST = ("original_id", "clock_id", "port_orientation", "integration_rule", "ports")
ROLE_SIGNS = {"natural_incident": 1, "natural_outgoing": -1,
              "controller_incident": 1, "controller_outgoing": -1, "load_output": -1}


def fraction(value: Any) -> Fraction:
    if not isinstance(value, str) or not value.strip():
        raise ValueError("every numerical input must be a nonempty exact decimal or fraction string")
    answer = Fraction(value)
    if answer.denominator == 0:
        raise ValueError("zero denominator")
    return answer


def exact_str(x: Fraction) -> str:
    return str(x.numerator) if x.denominator == 1 else f"{x.numerator}/{x.denominator}"


def mul_interval(a: tuple[Fraction, Fraction], b: tuple[Fraction, Fraction]) -> tuple[Fraction, Fraction]:
    products = (a[0] * b[0], a[0] * b[1], a[1] * b[0], a[1] * b[1])
    return min(products), max(products)


def add_interval(a, b):
    return a[0] + b[0], a[1] + b[1]


def minus_interval(a, b):
    return a[0] - b[1], a[1] - b[0]


def _file(root: Path, rel: str) -> Path:
    if not isinstance(rel, str) or not rel or Path(rel).is_absolute():
        raise ValueError("port file path must be a relative file under the evidence root")
    f = (root / rel).resolve(strict=True)
    if not f.is_relative_to(root) or not f.is_file():
        raise ValueError("port file escapes evidence root or is not a regular file")
    return f


def parse_port(path: Path) -> tuple[list[Fraction], list[tuple[Fraction, Fraction]]]:
    with path.open("r", encoding="utf-8-sig", newline="") as stream:
        reader = csv.DictReader(stream)
        if reader.fieldnames is None or tuple(reader.fieldnames) != FIELDS:
            raise ValueError(f"{path.name}: expected exact CSV columns {FIELDS}")
        times: list[Fraction] = []
        power: list[tuple[Fraction, Fraction]] = []
        for i, row in enumerate(reader, start=2):
            if None in row or any(row[name] is None for name in FIELDS):
                raise ValueError(f"{path.name}:{i}: malformed CSV")
            t, v, a, dv, da = (fraction(row[name]) for name in FIELDS)
            if dv < 0 or da < 0:
                raise ValueError(f"{path.name}:{i}: negative uncertainty radius")
            if times and t <= times[-1]:
                raise ValueError(f"{path.name}:{i}: nonincreasing or repeated sample time")
            times.append(t)
            power.append(mul_interval((v - dv, v + dv), (a - da, a + da)))
    if len(times) < 2:
        raise ValueError(f"{path.name}: at least two synchronous samples required")
    return times, power


def integrate_trapezoid(times, powers):
    """Conditional trapezoidal integral of piecewise linearly interpolated POWER.
    This does NOT certify sub-sample waveform aliasing/interpolation error.
    """
    total = Fraction(0), Fraction(0)
    for i in range(len(times) - 1):
        dt = (times[i + 1] - times[i]) / 2
        total = add_interval(total, (dt * (powers[i][0] + powers[i + 1][0]),
                                     dt * (powers[i][1] + powers[i + 1][1])))
    return total


def calculate(manifest: dict[str, Any], root: Path) -> dict[str, Any]:
    root = root.resolve()
    missing = [name for name in REQUIRED_MANIFEST if name not in manifest]
    if missing:
        raise ValueError(f"missing manifest fields: {missing}")
    for name in ("original_id", "clock_id"):
        if not isinstance(manifest[name], str) or not manifest[name].strip():
            raise ValueError(f"empty {name}")
    if manifest["port_orientation"] != "positive_in_port_direction":
        raise ValueError("require explicit signed positive_in_port_direction orientation")
    if manifest["integration_rule"] != "piecewise_linear_power_trapezoid":
        raise ValueError("only explicitly admitted piecewise-linear power integration is implemented")
    ports = manifest["ports"]
    if not isinstance(ports, dict) or set(ports) != set(PORTS):
        raise ValueError(f"all and only five original port roles must appear: {PORTS}")
    seen_paths: set[Path] = set()
    seen_hashes: set[str] = set()
    grid = None
    bounds: dict[str, tuple[Fraction, Fraction]] = {}
    for role in PORTS:
        entry = ports[role]
        if not isinstance(entry, dict) or set(entry) != {
            "file", "sha256", "clock_id", "integration_error_bound_J",
            "integration_error_certificate", "integration_error_certificate_sha256"
        }:
            raise ValueError(
                f"{role}: expected file, sha256, clock_id and independently "
                "traceable integration-error bound/certificate"
            )
        if entry["clock_id"] != manifest["clock_id"]:
            raise ValueError(f"{role}: clock mismatch")
        path = _file(root, entry["file"])
        sha = hashlib.sha256(path.read_bytes()).hexdigest()
        if sha != entry["sha256"] or path in seen_paths or sha in seen_hashes:
            raise ValueError(f"{role}: wrong SHA256, duplicate file, or duplicate evidence bytes")
        seen_paths.add(path)
        seen_hashes.add(sha)
        # The finite grid does not bound the real between-sample energy:
        # high-frequency V/I switching could evade the sampled envelope.
        # Require a separately archived bound, then widen the work interval.
        remainder = fraction(entry["integration_error_bound_J"])
        if remainder < 0:
            raise ValueError(f"{role}: negative integration remainder radius")
        remainder_file = _file(root, entry["integration_error_certificate"])
        remainder_sha = hashlib.sha256(remainder_file.read_bytes()).hexdigest()
        if (remainder_sha != entry["integration_error_certificate_sha256"]
                or remainder_file in seen_paths or remainder_sha in seen_hashes):
            raise ValueError(
                f"{role}: invalid or reused integration-error certificate"
            )
        seen_paths.add(remainder_file)
        seen_hashes.add(remainder_sha)
        t, p = parse_port(path)
        if grid is None:
            grid = t
        if t != grid:
            raise ValueError(f"{role}: nonidentical original time grid")
        trap = integrate_trapezoid(t, p)
        bounds[role] = (trap[0] - remainder, trap[1] + remainder)
    natural = minus_interval(bounds["natural_incident"], bounds["natural_outgoing"])
    controller = minus_interval(bounds["controller_incident"], bounds["controller_outgoing"])
    receiver = bounds["load_output"]
    # Positive remaining energy can be legitimate heat/storage or missing
    # sinks; negative remaining energy rejects a *fully accounted* balance.
    unassigned = minus_interval(add_interval(natural, controller), receiver)
    def serialize(interval):
        return {"lower_J": exact_str(interval[0]), "upper_J": exact_str(interval[1])}
    return {
        "original_id": manifest["original_id"], "clock_id": manifest["clock_id"],
        "sample_count": len(grid), "integration_rule": manifest["integration_rule"],
        "integration_remainder_certificate_required": True,
        "conditional_port_work": {role: serialize(v) for role, v in bounds.items()},
        "net_environmental_work": serialize(natural),
        "net_controller_work": serialize(controller),
        "useful_load_work": serialize(receiver),
        "unassigned_loss_or_storage_change": serialize(unassigned),
        "conditional_positive_environment_interval": natural[0] > 0,
        "conditional_balance_compatible_with_nonnegative_missing_sinks": unassigned[1] >= 0,
        "physical_claim_closed": False, "f15_closed": False,
        "reasons_not_acceptance": [
            "CSV numeric and calibration radii are not authenticated original SI measurements",
            "no independent source identification/replenishment certificate",
            "integration remainder bounds are supplied by external certificates, not independently validated by this reader",
            "no all-storage return, material/ionisation/thermal/radiation loss audit",
            "no proof of the original full-vector Maxwell-to-terminal port equality",
        ],
    }


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("manifest", type=Path)
    p.add_argument("--root", type=Path, required=True)
    p.add_argument("--out", type=Path)
    args = p.parse_args()
    try:
        data = json.loads(args.manifest.read_text(encoding="utf-8"))
        if not isinstance(data, dict):
            raise ValueError("manifest must be an object")
        result = calculate(data, args.root)
    except (ValueError, OSError, KeyError, TypeError, csv.Error) as error:
        print(json.dumps({"error": str(error), "physical_claim_closed": False}))
        return 2
    rendered = json.dumps(result, indent=2, sort_keys=True)
    if args.out:
        args.out.write_text(rendered + "\n", encoding="utf-8")
    print(rendered)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
