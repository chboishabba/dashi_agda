#!/usr/bin/env python3
"""Audit the static exponents of the fixed-torus Navier--Stokes scale map."""

from __future__ import annotations

import argparse
import json
from pathlib import Path


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("base", type=Path)
    parser.add_argument("scaled", type=Path)
    parser.add_argument("--output-json", type=Path)
    return parser.parse_args()


def candidate(payload: dict) -> dict:
    return payload["static_candidates_ranked"][0]


def relative_error(actual: float, expected: float) -> float:
    return abs(actual - expected) / max(1.0e-30, abs(expected))


def main() -> None:
    args = parse_args()
    base_payload = json.loads(args.base.read_text())
    scaled_payload = json.loads(args.scaled.read_text())
    base = candidate(base_payload)
    scaled = candidate(scaled_payload)
    wavelength_scale = 2 ** (
        scaled_payload["inputs"]["target_shell"] - base_payload["inputs"]["target_shell"]
    )
    packet_factor = float(wavelength_scale ** 3)
    rate_factor = float(wavelength_scale ** 5)
    observed_packet_factor = scaled["target_packet"] / base["target_packet"]
    observed_nonlinear_factor = scaled["target_nonlinear_rate"] / base["target_nonlinear_rate"]
    observed_viscous_factor = scaled["target_viscous_rate"] / base["target_viscous_rate"]
    tolerance = 1.0e-10
    report = {
        "contract": "ns_fixed_torus_dyadic_scaling_covariance_audit",
        "authority": {
            "finite_static_audit_only": True,
            "theorem_authority": False,
            "clay_authority": False,
        },
        "scale": wavelength_scale,
        "expected": {
            "packet_factor": packet_factor,
            "nonlinear_rate_factor": rate_factor,
            "viscous_rate_factor": rate_factor,
            "critical_mass_factor": packet_factor,
        },
        "observed": {
            "packet_factor": observed_packet_factor,
            "nonlinear_rate_factor": observed_nonlinear_factor,
            "viscous_rate_factor": observed_viscous_factor,
            "replenishment_ratio_base": base["initial_replenishment_ratio"],
            "replenishment_ratio_scaled": scaled["initial_replenishment_ratio"],
        },
        "relative_errors": {
            "packet": relative_error(observed_packet_factor, packet_factor),
            "nonlinear_rate": relative_error(observed_nonlinear_factor, rate_factor),
            "viscous_rate": relative_error(observed_viscous_factor, rate_factor),
            "replenishment_ratio": relative_error(
                scaled["initial_replenishment_ratio"], base["initial_replenishment_ratio"]
            ),
        },
    }
    report["finite_static_scaling_audit_passes"] = all(
        error <= tolerance for error in report["relative_errors"].values()
    )
    report["decision"] = (
        "literal dyadic copies are scaling-conjugate diagnostics; quotient them out and test "
        "non-self-similar profile geometry instead"
        if report["finite_static_scaling_audit_passes"] else
        "scaling covariance failed; repair the finite carrier or normalization before comparison"
    )
    rendered = json.dumps(report, indent=2, sort_keys=True)
    if args.output_json:
        args.output_json.parent.mkdir(parents=True, exist_ok=True)
        args.output_json.write_text(rendered + "\n")
    print(rendered)


if __name__ == "__main__":
    main()
