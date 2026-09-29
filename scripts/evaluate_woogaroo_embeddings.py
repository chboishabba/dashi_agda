#!/usr/bin/env python3
"""Woogaroo Earth-embedding four-arm evaluation, with strict leakage checks.

Usage:
  python scripts/evaluate_woogaroo_embeddings.py observations.csv output.json

Each row: cell,year,fold,target,baseline,alpha,tessera,fused,source_id,
         model_version,acquisition_quality,ground_truth_reference
fold is 'train' or 'test'. The four *_prediction columns must be
OUT-OF-SAMPLE predictions produced by separately trained heads; this script
does not train them, download imagery, or treat a source ID as calibration.
No values are fabricated or silently imputed.
"""
import csv
import json
import math
import sys
from collections import defaultdict
from pathlib import Path

REQUIRED = {
    "cell", "year", "fold", "target", "baseline", "alpha", "tessera",
    "fused", "source_id", "model_version", "acquisition_quality",
    "ground_truth_reference",
}
ARMS = ("baseline", "alpha", "tessera", "fused")


def require_unique_and_disjoint(rows):
    seen = set()
    cells = defaultdict(set)
    years = defaultdict(set)
    for index, row in enumerate(rows, start=2):
        if row["fold"] not in ("train", "test"):
            raise ValueError(f"row {index}: invalid fold")
        key = (row["cell"], row["year"])
        if key in seen:
            raise ValueError(f"row {index}: duplicate cell/year {key}")
        seen.add(key)
        if not all(row[name].strip() for name in REQUIRED):
            raise ValueError(f"row {index}: missing mandatory provenance")
        cells[row["fold"]].add(row["cell"])
        years[row["fold"]].add(row["year"])
    if cells["train"] & cells["test"]:
        raise ValueError("spatial leakage: cells shared across folds")
    if years["train"] & years["test"]:
        raise ValueError("temporal leakage: years shared across folds")
    return {"train_cells": len(cells["train"]), "test_cells": len(cells["test"]),
            "train_years": sorted(years["train"]),
            "test_years": sorted(years["test"])}


def score(rows, arm):
    pairs = [(float(r["target"]), float(r[arm])) for r in rows]
    if not pairs:
        raise ValueError("at least one held-out prediction required")
    if not all(math.isfinite(x) and math.isfinite(y) for x, y in pairs):
        raise ValueError("nonfinite measurement or prediction")
    count = len(pairs)
    mae = sum(abs(a-b) for a,b in pairs) / count
    rmse = math.sqrt(sum((a-b)**2 for a,b in pairs) / count)
    return {"count": count, "MAE": mae, "RMSE": rmse}


def evaluate(path):
    with Path(path).open(newline="", encoding="utf-8") as file:
        reader = csv.DictReader(file)
        if not REQUIRED.issubset(set(reader.fieldnames or ())):
            raise ValueError(f"missing columns: {sorted(REQUIRED-set(reader.fieldnames or ()))}")
        rows = list(reader)
    if not rows or not any(row["fold"] == "train" for row in rows):
        raise ValueError("both training and test metadata must be supplied")
    partition = require_unique_and_disjoint(rows)
    heldout = [row for row in rows if row["fold"] == "test"]
    if not heldout:
        raise ValueError("empty heldout fold")
    metrics = {arm: score(heldout, arm) for arm in ARMS}
    return {
        "protocol": "Woogaroo geospatial holdout v1",
        "status": "evaluated supplied predictions only; no model trained",
        "partition": partition,
        "heldout_metrics": metrics,
        "provenance_rows": len(rows),
        "source_ids": sorted(set(row["source_id"] for row in rows)),
        "model_versions": sorted(set(row["model_version"] for row in rows)),
        "acquisition_quality_labels": sorted(set(row["acquisition_quality"] for row in rows)),
        "warning": "Fold disjointness does not certify geographic buffer distance or independent labels.",
    }


def main():
    if len(sys.argv) != 3:
        raise SystemExit("usage: evaluate_woogaroo_embeddings.py IN.csv OUT.json")
    result = evaluate(sys.argv[1])
    Path(sys.argv[2]).write_text(json.dumps(result, indent=2)+"\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
