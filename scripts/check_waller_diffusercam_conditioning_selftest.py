#!/usr/bin/env python3
"""Offline numerical self-test for the DiffuserCam conditioning audit.

This module deliberately uses synthetic PSF stacks only.  It verifies that the
source-H impulse-column compiler agrees with literal FFT convolution for both
odd and even array shapes and stress-checks the mutual-coherence/Gershgorin
lower-bound compiler on random finite supports.

Passing this test validates implementation mathematics only.  It does not
materialise the public Berkeley/Waller PSF artifact, pay a real-data
conditioning receipt, or establish physical photon calibration.
"""

from __future__ import annotations

import importlib.util
import json
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
AUDIT_PATH = HERE / "check_waller_diffusercam_conditioning.py"


def _load_audit_module():
    spec = importlib.util.spec_from_file_location("waller_conditioning_audit", AUDIT_PATH)
    if spec is None or spec.loader is None:
        raise RuntimeError("could not load conditioning audit module")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def synthetic_operator_self_test(seed: int = 1729) -> dict:
    audit = _load_audit_module()
    rng = np.random.default_rng(seed)

    shapes = [(6, 8, 5), (5, 7, 4), (5, 6, 3), (4, 5, 2)]
    max_fft_error = 0.0
    supports_checked = 0
    violations = 0
    worst_margin = float("inf")

    for shape in shapes:
        calibrated = rng.normal(size=shape)
        columns, labels, fft_error, _ = audit.source_forward_selected_columns(
            calibrated,
            lateral_radius=1,
            lateral_step=1,
        )
        if len(labels) != columns.shape[1]:
            raise AssertionError("column labels do not match selected H columns")

        max_fft_error = max(max_fft_error, float(fft_error))

        mu, min_column_norm = audit.translated_column_mutual_coherence(columns)
        max_order = min(4, columns.shape[1])

        for sparse_order in range(1, max_order + 1):
            normalized_lower = audit.gershgorin_sparse_lower_bound(mu, sparse_order)
            unnormalized_lower = (min_column_norm**2) * normalized_lower

            trials = min(32, max(1, columns.shape[1]))
            for _ in range(trials):
                support = rng.choice(columns.shape[1], size=sparse_order, replace=False)
                gram = columns[:, support].T @ columns[:, support]
                observed_lower = float(np.linalg.eigvalsh(gram)[0])
                margin = observed_lower - unnormalized_lower
                worst_margin = min(worst_margin, margin)
                supports_checked += 1
                if margin < -1e-10:
                    violations += 1

    return {
        "synthetic_only": True,
        "real_psf_receipt": False,
        "physical_photon_calibration": False,
        "source_operator_identity_tested": True,
        "sparse_bound_compiler_tested": True,
        "seed": int(seed),
        "shapes_checked": len(shapes),
        "max_fft_vs_roll_abs_error": float(max_fft_error),
        "gershgorin_supports_checked": int(supports_checked),
        "gershgorin_bound_violations": int(violations),
        "worst_observed_minus_bound_margin": float(worst_margin),
    }


def main() -> None:
    result = synthetic_operator_self_test()
    print(json.dumps(result, indent=2, sort_keys=True, allow_nan=False))
    if result["max_fft_vs_roll_abs_error"] >= 1e-12:
        raise SystemExit("FFT-vs-roll source-H identity exceeded tolerance")
    if result["gershgorin_bound_violations"] != 0:
        raise SystemExit("synthetic sparse Gram test violated Gershgorin lower bound")


if __name__ == "__main__":
    main()
