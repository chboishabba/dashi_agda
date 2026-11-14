#!/usr/bin/env python3
"""Source-pinned exploratory holdout for original Kuo et al. dmsC measurements.

Original data: cmarti/shine_dalgarno/data/dmsc.csv (Git blob
151cd87272cbdd6bcc2b1e70bdfd2a4ea2933d2c), using only original
dmsC.1 / dmsC.2 / dmsC.3 columns, never posterior/inferred landscape values.

A genotype is one observational unit: available replicate values are averaged,
not independently assigned to train/test.  Deterministic FNV-1a32 split
(70/15/15) with salt dashi-2026-v1. Train four OLS count models:
intercept; intercept+G; +G+C; +G+C+U. Select by VALIDATION RMSE.
One held-out TEST read; 600 genotype bootstrap draws.

These are predictive associations with bacterial SD translation readout,
not proof of a mechanistic theory or of a developmental attractor.
"""
from __future__ import annotations

import argparse
import csv
import hashlib
import json
import math
from pathlib import Path

import numpy as np

ORIGINAL_BLOB = "151cd87272cbdd6bcc2b1e70bdfd2a4ea2933d2c"
COLUMNS = ("Genotype", "dmsC.1", "dmsC.2", "dmsC.3")
SALT = "dashi-2026-v1"
FEATURES = ((), ("g",), ("g", "c"), ("g", "c", "u"))


def fnv1a32_fraction(payload: str) -> float:
    h = 2166136261
    for char in payload:
        h = ((h ^ ord(char)) * 16777619) & 0xFFFFFFFF
    return h / 4294967296.


def assignment(seq: str) -> str:
    x = fnv1a32_fraction(SALT + ":" + seq)
    return "train" if x < .7 else "validation" if x < .85 else "test"


def input_measurements(path: Path):
    raw=path.read_bytes()
    with path.open(newline="") as f:
        reader=csv.DictReader(f)
        if not set(COLUMNS).issubset(reader.fieldnames or []):
            raise ValueError("expected original Kuo dmsC columns")
        record=[];seen=set();raw_count=0;rep_hist={k:0 for k in range(4)}
        for line,row in enumerate(reader,2):
            raw_count+=1
            seq=(row["Genotype"] or "").strip().upper()
            if len(seq)!=9 or any(c not in "ACGU" for c in seq):
                raise ValueError(f"invalid 9-mer at source row {line}")
            if seq in seen:
                raise ValueError("duplicate source genotype")
            seen.add(seq)
            values=[]
            for name in COLUMNS[1:]:
                value=(row[name] or "").strip()
                if value and value.lower() not in ("nan","na","null"):
                    num=float(value)
                    if not math.isfinite(num):
                        raise ValueError(f"nonfinite replicate at source row {line}")
                    values.append(num)
            rep_hist[len(values)]+=1
            if not values:
                continue
            record.append({
                "seq":seq, "y":sum(values)/len(values),
                "g":seq.count("G"),"c":seq.count("C"),"u":seq.count("U"),
                "split":assignment(seq), "replicates":len(values)
            })
    if raw_count!=len(seen):
        raise ValueError("source rows are not unique")
    if not record:
        raise ValueError("no measured source genotypes")
    cohorts={k:[r for r in record if r["split"]==k]
             for k in ("train","validation","test")}
    if min(len(group) for group in cohorts.values())<2:
        raise ValueError("invalid heldout split")
    return cohorts, {
        "source_git_blob": ORIGINAL_BLOB,
        "source_sha256": hashlib.sha256(raw).hexdigest(),
        "original_sequence_rows":raw_count,
        "measured_genotypes":len(record),
        "replicate_coverage":rep_hist,
        "original_observed_replicates":sum(r["replicates"] for r in record),
        "split_counts":{k:len(v) for k,v in cohorts.items()},
    }


def predictor_matrix(group, features):
    return np.asarray([[1.]+[float(r[f]) for f in features] for r in group],
                      dtype=float)


def test_metrics(group, coefficients, features):
    X=predictor_matrix(group,features)
    y=np.asarray([r["y"] for r in group],dtype=float)
    pred=X @ coefficients
    errors=pred-y
    return {
        "rmse":float(np.sqrt(np.mean(errors**2))),
        "mae":float(np.mean(abs(errors))),
        "r2":float(1.-sum(errors**2)/sum((y-np.mean(y))**2)),
        "n_genotypes":len(group),
    }, errors


def replicate_bootstrap(e,baseline,n_bootstrap=600):
    # Explicit xorshift32 sampling, matching the checked JavaScript
    # first-source-examination receipt. Bootstrap units are genotypes.
    n=len(e)
    state=0x7f17329f
    x=e*e
    b=baseline*baseline
    draws=np.empty((n_bootstrap,3),dtype=float)
    for rep in range(n_bootstrap):
        se=sb=0.
        for _ in range(n):
            state ^= (state << 13) & 0xFFFFFFFF
            state &= 0xFFFFFFFF
            state ^= state >> 17
            state ^= (state << 5) & 0xFFFFFFFF
            state &= 0xFFFFFFFF
            j=(state*n)>>32
            se+=float(x[j]);sb+=float(b[j])
        rmse=math.sqrt(se/n)
        base=math.sqrt(sb/n)
        draws[rep]=[rmse,base,(base-rmse)/base]
    intervals=np.percentile(draws,[2.5,97.5],axis=0)
    return {
        "reps":n_bootstrap,"seed":"xorshift32 0x7f17329f",
        "rmse_95_percentile":list(map(float,intervals[:,0])),
        "baseline_rmse_95_percentile":list(map(float,intervals[:,1])),
        "fractional_improvement_95_percentile":list(map(float,intervals[:,2])),
    }


def benchmark(path, n_bootstrap=600):
    groups,source=input_measurements(path)
    candidates=[]
    for features in FEATURES:
        A=predictor_matrix(groups["train"],features)
        y=np.asarray([r["y"] for r in groups["train"]],dtype=float)
        coeff=np.linalg.lstsq(A,y,rcond=None)[0]
        val,_=test_metrics(groups["validation"],coeff,features)
        candidates.append({"features":list(features),
                           "coefficients":coeff.tolist(),
                           "validation":val})
    candidates.sort(key=lambda x:x["validation"]["rmse"])
    chosen=candidates[0]
    model,errors=test_metrics(groups["test"],
                             np.asarray(chosen["coefficients"]),
                             chosen["features"])
    null=[c for c in candidates if not c["features"]][0]
    null_test,null_error=test_metrics(
        groups["test"],np.asarray(null["coefficients"]),())
    return {
        "status":"primary-measured-holdout-predictive-association-only",
        "source":source,
        "model_selection":"validation-only",
        "candidate_validation":candidates,
        "selected_features":chosen["features"],
        "test":model,
        "training_mean_baseline_test":null_test,
        "test_rmse_fractional_improvement":
            (null_test["rmse"]-model["rmse"])/null_test["rmse"],
        "bootstrap":replicate_bootstrap(errors,null_error,n_bootstrap),
        "model_is_biological_developmental_attractor":False,
        "source_sequence_measurement_is_prospective_perturbation":False,
        "pnf_mutation_performed":False,
    }


def self_test():
    import tempfile
    from itertools import product
    with tempfile.TemporaryDirectory() as d:
        path=Path(d)/"input.csv"
        with path.open("w",newline="") as f:
            writer=csv.writer(f);writer.writerow(COLUMNS)
            for triplet in product("ACGU",repeat=5):
                seq="AAAA"+"".join(triplet)
                writer.writerow((seq,0.5+0.1*seq.count("G"),"",0.6))
        output=benchmark(path,n_bootstrap=30)
        assert output["source"]["measured_genotypes"]==1024
        assert output["source"]["replicate_coverage"][2]==1024
        assert output["test"]["n_genotypes"]>2
        assert output["pnf_mutation_performed"] is False
    print("PASS: original dmsC column contract, deterministic genotype-heldout OLS")
    print("SYNTHETIC SELF-TEST ONLY; empirical result requires original data")


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--original-csv",type=Path)
    parser.add_argument("--receipt",type=Path)
    parser.add_argument("--bootstrap",type=int,default=600)
    parser.add_argument("--self-test",action="store_true")
    args=parser.parse_args()
    if args.self_test:self_test();return
    if not args.original_csv or not args.receipt:
        parser.error("--original-csv and --receipt required")
    if args.bootstrap<30:
        parser.error("at least 30 bootstrap draws required")
    result=benchmark(args.original_csv,n_bootstrap=args.bootstrap)
    args.receipt.write_text(json.dumps(result,indent=2,sort_keys=True)+"\n")
    print(json.dumps({"source":result["source"],
                      "test":result["test"],
                      "bootstrap":result["bootstrap"]},indent=2))


if __name__=="__main__":
    main()
