#!/usr/bin/env python3
"""P3/P5 source-scoped, SI-explicit first-order kinetic calibration.

Selected model: dC/dt = influx - decay * C.
Units: C [mol/L], time [s], influx [mol/(L*s)], decay [1/s].
This *does not infer that actual biological data follow this model*.
Identifies two parameters from TRAIN experiments only, cluster bootstraps
their uncertainty, and evaluates independent held-out experiment IDs.
No data are downloaded, simulated and passed off as empirical, or sent to PNF.

CSV columns: source_id,experiment_id,split,time_s,initial_mol_l,
observed_mol_l,sigma_mol_l
split values are train, validation, test. Each experiment ID has one split
and one known initial concentration supplied independently of outcomes.
"""
from __future__ import annotations
import argparse
import csv
import hashlib
import json
from collections import Counter, defaultdict
from pathlib import Path

import numpy as np
from scipy.optimize import least_squares


REQUIRED = ("source_id", "experiment_id", "split", "time_s",
            "initial_mol_l", "observed_mol_l", "sigma_mol_l")


def read_assay(path):
    raw = Path(path).read_bytes()
    with Path(path).open(newline="") as stream:
        reader = csv.DictReader(stream)
        if not set(REQUIRED).issubset(reader.fieldnames or ()):
            raise ValueError("missing assay columns: " +
                             ", ".join(set(REQUIRED)-set(reader.fieldnames or ())))
        rows = list(reader)
    if not rows:
        raise ValueError("empty assay")
    out = []
    groups = {}
    for line, row in enumerate(rows, 2):
        try:
            ident = row["experiment_id"].strip()
            source = row["source_id"].strip()
            split = row["split"].strip().lower()
            t, initial, value, sigma = [
                float(row[key]) for key in REQUIRED[3:]]
        except (KeyError, TypeError, ValueError) as ex:
            raise ValueError(f"invalid assay line {line}: {ex}") from ex
        if not source or not ident or split not in ("train", "validation", "test"):
            raise ValueError(f"line {line}: missing source/id or invalid split")
        if not all(np.isfinite([t, initial, value, sigma])):
            raise ValueError(f"line {line}: nonfinite value")
        if t < 0 or initial < 0 or value < 0 or sigma <= 0:
            raise ValueError(f"line {line}: require nonnegative time/amount, sigma>0")
        if ident in groups and groups[ident] != (source, split, initial):
            raise ValueError(f"experiment {ident} changes source/split/initial state")
        groups[ident] = (source, split, initial)
        out.append((source, ident, split, t, initial, value, sigma))
    if len({x[0] for x in out}) != 1:
        raise ValueError("source IDs differ: calibration must be source scoped")
    for ident in groups:
        times = [x[3] for x in out if x[1] == ident]
        if len(times) != len(set(times)):
            raise ValueError(f"duplicate time within experiment {ident}")
    counts = Counter(split for _, split, _ in groups.values())
    if counts["train"] < 3 or counts["test"] < 1:
        raise ValueError("need >=3 distinct train experiments and >=1 held-out test")
    return out, hashlib.sha256(raw).hexdigest(), dict(counts)


def solution(t, c0, decay, influx):
    t = np.asarray(t, dtype=float)
    c0 = np.asarray(c0, dtype=float)
    if decay <= 0:
        return c0 + influx*t
    return c0*np.exp(-decay*t) - (influx/decay)*np.expm1(-decay*t)


def fit(train):
    a = np.asarray([[r[3], r[4], r[5], r[6]] for r in train], dtype=float)
    if len(a) < 5 or len(set(a[:, 0])) < 3:
        raise ValueError("insufficient independent measurement times")
    t, c0, y, sigma = a.T
    timescale = max(float(np.median(t[t > 0])) if np.any(t > 0) else 1., 1e-9)
    scale = max(float(np.median(y)), 1e-6)
    x0 = [1/timescale, scale/timescale]
    def residual(x):
        return (solution(t, c0, *x) - y)/sigma
    result = least_squares(residual, x0=x0,
                           bounds=([1e-12, 0], [1e8, 1e8]),
                           max_nfev=1500, xtol=1e-12, ftol=1e-12, gtol=1e-12)
    if not result.success or np.linalg.matrix_rank(result.jac) < 2:
        raise ValueError("model fit or two-parameter identifiability failed")
    return result.x


def metrics(rows, params):
    if not rows:
        return None
    array = np.asarray([[r[3], r[4], r[5], r[6]] for r in rows])
    t, c0, y, sig = array.T
    pred = solution(t, c0, *params)
    diff = pred-y
    return {
        "n_measurements": len(rows),
        "n_independent_experiments": len({r[1] for r in rows}),
        "rmse_mol_l": float(np.sqrt(np.mean(diff**2))),
        "mae_mol_l": float(np.mean(abs(diff))),
        "weighted_rmse_sigma": float(np.sqrt(np.mean((diff/sig)**2))),
        "null_initial_concentration_rmse_mol_l":
            float(np.sqrt(np.mean((c0-y)**2))),
    }


def calibration_report(rows, source_sha256, split_counts, bootstrap=200, seed=0):
    train = [r for r in rows if r[2] == "train"]
    by_id = defaultdict(list)
    for r in train:
        by_id[r[1]].append(r)
    params = fit(train)
    generator = np.random.default_rng(seed)
    ids = sorted(by_id)
    replicates = []
    failed = 0
    for _ in range(bootstrap):
        chosen = generator.choice(ids, size=len(ids), replace=True)
        sampled = [row for ident in chosen for row in by_id[ident]]
        try:
            replicates.append(fit(sampled))
        except ValueError:
            failed += 1
    if len(replicates) < max(30, bootstrap//2):
        raise ValueError("bootstrap identification inadequate; refuse confidence interval")
    intervals = np.percentile(np.asarray(replicates), [2.5, 97.5], axis=0)
    return {
        "status": "model-fit-only-not-mechanism-validated",
        "source_id": rows[0][0],
        "source_sha256": source_sha256,
        "model": "dC/dt = influx - decay*C",
        "units": {"time":"s", "concentration":"mol/L", "decay":"1/s",
                  "influx":"mol/(L*s)"},
        "decay_per_s": float(params[0]),
        "influx_mol_l_per_s": float(params[1]),
        "cluster_bootstrap_95_percentile_intervals": {
            "decay_per_s": [float(intervals[0,0]), float(intervals[1,0])],
            "influx_mol_l_per_s": [float(intervals[0,1]), float(intervals[1,1])],
        },
        "bootstrap_seed": seed, "bootstrap_success": len(replicates),
        "bootstrap_failed_rank": failed,
        "experiment_counts": split_counts,
        "train_metrics": metrics(train, params),
        "validation_metrics": metrics([r for r in rows if r[2]=="validation"], params),
        "test_metrics": metrics([r for r in rows if r[2]=="test"], params),
        "held_out_test_experiments_never_used_for_fit": True,
        "biological_mechanism_identified": False,
        "model_selection_validated": False,
        "pnf_mutation_performed": False,
    }


def self_test():
    import tempfile
    with tempfile.TemporaryDirectory() as d:
        path = Path(d)/"synthetic.csv"
        with path.open("w", newline="") as f:
            writer = csv.writer(f)
            writer.writerow(REQUIRED)
            for i in range(9):
                split = "train" if i<6 else ("validation" if i==6 else "test")
                c0 = 0.1 + i*0.03
                for t in (0., 1., 2., 4., 8.):
                    writer.writerow(("SYNTHETIC:NO-EXPERIMENT",str(i),split,
                                     t,c0,float(solution(t,c0,0.2,0.04)),0.01))
        rows, sha, groups = read_assay(path)
        r = calibration_report(rows, sha, groups, bootstrap=40,seed=27)
        assert abs(r["decay_per_s"]-0.2)<1e-7, r["decay_per_s"]
        assert abs(r["influx_mol_l_per_s"]-0.04)<1e-7
        assert r["test_metrics"]["rmse_mol_l"]<1e-7
        assert r["bootstrap_success"]>=30
        # Deliberately reject accidental training/test leakage.
        text=path.read_text().replace("2,test", "2,train")
        # The meaningful violation is an experiment whose split changes.
        with path.open("a") as f:
            f.write("SYNTHETIC:NO-EXPERIMENT,0,test,9,0.1,0.18,0.01\n")
        try: read_assay(path)
        except ValueError: pass
        else: raise AssertionError("train/test group leakage admitted")
        print("PASS: SI kinetics, 2-parameter fit, bootstrap, heldout groups, leakage rejection")
        print("SYNTHETIC ONLY; no real biological kinetics or model validation claimed")


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--assay",type=Path)
    p.add_argument("--output",type=Path)
    p.add_argument("--bootstrap",type=int,default=200)
    p.add_argument("--seed",type=int,default=0)
    p.add_argument("--self-test",action="store_true")
    a=p.parse_args()
    if a.self_test:
        self_test()
        return
    if not a.assay or not a.output:
        p.error("--assay and --output are required")
    if a.bootstrap<30:
        p.error("--bootstrap must be at least 30")
    rows,sha,groups=read_assay(a.assay)
    report=calibration_report(rows,sha,groups,a.bootstrap,a.seed)
    a.output.write_text(json.dumps(report,indent=2,sort_keys=True)+"\n")
    print(json.dumps({"status":report["status"],"source_sha256":sha,
                      "test_metrics":report["test_metrics"]}))


if __name__=="__main__":
    main()
