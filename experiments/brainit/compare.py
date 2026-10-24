"""Paired stimulus-level comparisons of Brain-IT input-control evaluations.

Deliberately no 'brain information percentage' estimator: paired differences
are metric contrasts, not a decomposition of a latent causal quantity.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

import numpy as np

SUPPORTED = ("pixcorr", "ssim")


def _index(report: dict) -> dict:
    rows = report.get("rows", [])
    result = {}
    for row in rows:
        key = (row["subject"], row["seed"], row["branch"], row["stimulus_id"])
        if key in result:
            raise ValueError(f"Duplicated subject/seed/branch/stimulus row {key}")
        result[key] = row
    if not result:
        raise ValueError("No stimulus-level rows")
    return result


def paired_contrast(paired_reports: list[dict], control_reports: list[dict],
                    draws: int = 2000, seed: int = 20261024) -> dict:
    if len(paired_reports) != len(control_reports) or not paired_reports:
        raise ValueError("Require the same positive number of paired and control reports")
    if draws < 100:
        raise ValueError("At least 100 bootstrap draws are required")
    values = {metric: [] for metric in SUPPORTED}
    subjects = set()
    conditions = set()
    all_keys = set()
    for p, c in zip(paired_reports, control_reports):
        if p.get("schema") != "brainit-reconstruction-evaluation-v1" or c.get(
            "schema") != "brainit-reconstruction-evaluation-v1":
            raise ValueError("Unrecognised evaluation report schema")
        if p["condition"] != "paired" or c["condition"] not in ("deranged", "zero"):
            raise ValueError("Need paired signal versus explicit input control")
        if p["metric_version"] != c["metric_version"]:
            raise ValueError("Metric implementations mismatch")
        if p["artifact_hashes"]["images"] != c["artifact_hashes"]["images"]:
            raise ValueError("Reference images differ between conditions")
        a, b = _index(p), _index(c)
        if set(a) != set(b):
            raise ValueError("Pairing broken: subject/seed/branch/stimulus IDs differ")
        if all_keys.intersection(a):
            raise ValueError("Duplicate sample between report pairs")
        all_keys.update(a)
        subjects.update(k[0] for k in a)
        conditions.add(c["condition"])
        for key in sorted(a):
            for metric in SUPPORTED:
                pa, co = a[key].get(metric), b[key].get(metric)
                if pa is None or co is None:
                    raise ValueError(f"Undefined {metric} at {key}; report separately")
                if not np.isfinite(pa) or not np.isfinite(co):
                    raise ValueError(f"Nonfinite metric {metric} at {key}")
                values[metric].append(float(pa - co))
    rng = np.random.default_rng(seed)
    metrics = {}
    for name, differences in values.items():
        d = np.asarray(differences)
        boots = np.mean(d[rng.integers(0, len(d), size=(draws, len(d)))], axis=1)
        metrics[name] = {
            "n_paired_rows": len(d), "paired_minus_control": float(d.mean()),
            "bootstrap_ci95": [float(x) for x in np.quantile(boots, [0.025, 0.975])],
            "effect_direction": "positive means paired signal outperformed input control",
        }
    return {
        "schema": "brainit-paired-contrast-v1",
        "conditions": sorted(conditions),
        "subjects_observed_only": sorted(subjects),
        "n_test_rows": len(all_keys),
        "n_bootstrap_draws": draws, "bootstrap_seed": seed,
        "uncertainty_scope": "stimulus-level resampling within observed subjects; "
                             "not an across-subject population confidence interval",
        "metrics": metrics,
        "claim_boundary": "Metric deltas are not an identifiable percentage "
                          "of decoded neural information or proof of causality.",
    }


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--paired", type=Path, nargs="+", required=True)
    ap.add_argument("--control", type=Path, nargs="+", required=True)
    ap.add_argument("--draws", type=int, default=2000)
    ap.add_argument("--seed", type=int, default=20261024)
    ap.add_argument("--out", type=Path, required=True)
    args = ap.parse_args(argv)
    p = [json.loads(x.read_text()) for x in args.paired]
    c = [json.loads(x.read_text()) for x in args.control]
    report = paired_contrast(p, c, args.draws, args.seed)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(json.dumps(report["metrics"], indent=2))


if __name__ == "__main__":
    main()
