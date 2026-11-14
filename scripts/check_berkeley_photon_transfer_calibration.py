#!/usr/bin/env python3
"""Synthetic execution check for the Berkeley photon-transfer calibration algebra.

This validates the compiler shape used by the executed Berkeley notebook:
Poisson photon counts -> affine digital counts -> variance-vs-mean slope fit ->
(digital - intercept) / slope recovery. It deliberately does not claim that the
multi-GB Berkeley grayscale sweep was re-executed locally and does not calibrate
incident optical throughput across encoders.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import numpy as np
from scipy.stats import linregress

SEED = 1729
LEVELS = np.linspace(50.0, 2000.0, 250)
PIXELS_PER_LEVEL = 4096
VALIDATION_PHOTON_MEAN = 800.0
VALIDATION_PIXELS = 20000

SYSTEMS = {
    "rml": {"slope": 0.02, "intercept": 1.46, "fit_start": 150, "fit_end": 250},
    "diffuser": {"slope": 0.03, "intercept": 0.36, "fit_start": 150, "fit_end": 250},
    "lensed": {"slope": 0.05, "intercept": 0.01, "fit_start": 175, "fit_end": 250},
}


def variance_vs_mean(means: np.ndarray, variances: np.ndarray, start: int, end: int):
    return linregress(means[start:end], variances[start:end])


def digital_to_photons(digital: np.ndarray, slope: float, intercept: float) -> np.ndarray:
    return (digital - intercept) / slope


def run() -> dict:
    rng = np.random.default_rng(SEED)
    system_results = {}
    for name, p in SYSTEMS.items():
        means = []
        variances = []
        for photon_mean in LEVELS:
            photons = rng.poisson(photon_mean, size=PIXELS_PER_LEVEL).astype(float)
            digital = p["slope"] * photons + p["intercept"]
            means.append(float(np.mean(digital)))
            variances.append(float(np.var(digital)))

        fit = variance_vs_mean(
            np.asarray(means),
            np.asarray(variances),
            p["fit_start"],
            p["fit_end"],
        )

        photons = rng.poisson(VALIDATION_PHOTON_MEAN, size=VALIDATION_PIXELS).astype(float)
        digital = p["slope"] * photons + p["intercept"]
        recovered = digital_to_photons(digital, p["slope"], p["intercept"])

        system_results[name] = {
            "source_display_slope": p["slope"],
            "source_display_intercept": p["intercept"],
            "fit_slope": float(fit.slope),
            "fit_intercept": float(fit.intercept),
            "fit_r2": float(fit.rvalue**2),
            "relative_slope_error": float(abs(fit.slope - p["slope"]) / p["slope"]),
            "max_inverse_abs_error": float(np.max(np.abs(recovered - photons))),
        }

    return {
        "receipt_kind": "synthetic_photon_transfer_compiler_validation",
        "seed": SEED,
        "systems": system_results,
        "compiler_formula": "(digital - intercept) / slope",
        "raw_berkeley_sweep_reexecuted": False,
        "source_executed_notebook_reproduced_from_raw_data": False,
        "incident_throughput_calibrated": False,
        "matched_physical_photon_budget": False,
        "synthetic_only": True,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()
    result = run()
    encoded = json.dumps(result, indent=2, sort_keys=True) + "\n"
    print(encoded, end="")
    if args.json_out is not None:
        args.json_out.write_text(encoded, encoding="utf-8")


if __name__ == "__main__":
    main()
