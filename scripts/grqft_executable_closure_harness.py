#!/usr/bin/env python3
from __future__ import annotations
import argparse, json
from pathlib import Path

def load(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))

def build(einstein: dict, w4: dict) -> dict:
    if einstein["unique_zero_residual_kappa"] != [1]:
        raise AssertionError("Einstein normalized zero-residual set changed")
    cal = w4["calibration"]
    if float(cal["chi2PerDof"]) <= 3.0:
        raise AssertionError("W4 dirty candidate no longer satisfies hard-negative guard")
    bins = w4["per_bin"]
    return {
        "artifactSchema": "dashi-grqft-executable-closure-matrix-v1",
        "finiteEinstein": {
            "status": "locally_closed",
            "uniqueNormalizedKappa": 1,
            "testedKappas": [row["kappa_normalized"] for row in einstein["runs"]],
        },
        "w4Calibration": {
            "status": "locally_rejected",
            "scale": cal["scale"],
            "chi2": cal["chi2"],
            "dof": cal["dof"],
            "chi2PerDof": cal["chi2PerDof"],
            "firstBinPull": bins[0]["pull"],
            "lastBinPull": bins[-1]["pull"],
            "projectionDigest": w4["projectionDigest"],
            "replacementRequired": True,
        },
        "sameCandidateGRRecovery": {
            "status": "analytic_realization_missing",
            "firstMissing": "missingDiscreteToSmoothCurvatureConvergence",
            "weakFieldFirstMissing": "missingRadialValuation",
        },
        "sameCandidateQFTRecovery": {"status": "concrete_instance_missing"},
        "sameCarrierStressWeld": {"status": "concrete_instance_missing"},
        "physicalUnitCalibration": {
            "status": "local_adapter_present_external_acceptance_required",
            "localCoverage": [
                "physicalUnitCarrier",
                "physicalDimensionVector",
                "natToUnitCalibrationMap",
                "calibratedQuotientScaleMap",
                "factorization",
                "dimensionalPreservation",
            ],
        },
        "empiricalGRQFTValidation": {"status": "external_information_required"},
        "terminalPromotion": False,
    }

def main() -> None:
    p = argparse.ArgumentParser()
    p.add_argument("--einstein", type=Path, default=Path("outputs/grqft_einstein_bidi_residual.json"))
    p.add_argument("--w4", type=Path, default=Path("logs/research/w4_z_peak_anchor_dirty_run_20260513.json"))
    p.add_argument("--output", type=Path, default=Path("outputs/grqft_executable_closure_matrix.json"))
    a = p.parse_args()
    result = build(load(a.einstein), load(a.w4))
    a.output.parent.mkdir(parents=True, exist_ok=True)
    a.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2, sort_keys=True))

if __name__ == "__main__":
    main()
