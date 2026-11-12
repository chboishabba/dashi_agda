#!/usr/bin/env python3
"""Reproducible, no-lookahead Cybersyn scenario model comparison.

Compares an additive logistic model with a four-interaction model on a
chronological holdout. Both models are statistical candidates, not causal
forecasts. No source self-attestation upgrades empirical authority.

Data columns: region,time,event_id, energy,food,climate,fx_funding,ai_credit,
housing,infrastructure,outcome, equity_loss,lender_loss,public_loss,total_loss,
grid_ai,grid_households,grid_other,grid_unused,grid_total, labour_housing,
labour_datacentre,labour_other,labour_total.
"""
from __future__ import annotations

import argparse
import csv
from datetime import datetime
from hashlib import sha256
import io
import json
from math import exp, log
from pathlib import Path
import random

BASE = ("energy", "food", "climate", "fx_funding", "ai_credit",
        "housing", "infrastructure")
INTERACTIONS = (("energy", "food"), ("fx_funding", "ai_credit"),
                ("climate", "infrastructure"), ("housing", "fx_funding"))
AMOUNTS = ("equity_loss", "lender_loss", "public_loss", "total_loss",
           "grid_ai", "grid_households", "grid_other", "grid_unused",
           "grid_total", "labour_housing", "labour_datacentre",
           "labour_other", "labour_total")


class ScenarioError(ValueError):
    pass


def parse_time(value: str) -> datetime:
    try:
        date = datetime.fromisoformat(value.replace("Z", "+00:00"))
    except (TypeError, ValueError) as exc:
        raise ScenarioError("invalid timestamp") from exc
    if date.tzinfo is None or date.utcoffset().total_seconds() != 0:
        raise ScenarioError("only explicit UTC timestamps accepted")
    return date


def load(raw: bytes, manifest: dict) -> list[dict]:
    if manifest.get("schema") != "dashi-cybersyn-empirical-scenario-v1":
        raise ScenarioError("invalid dataset manifest schema")
    if sha256(raw).hexdigest() != manifest.get("sha256"):
        raise ScenarioError("source snapshot hash mismatch")
    for key in ("dataset_id", "version", "attribution_owner",
                "source_locator", "licence", "collection_method", "source_layer"):
        if not isinstance(manifest.get(key), str) or not manifest[key].strip():
            raise ScenarioError("missing source provenance " + key)
    if manifest.get("empirically_admitted") is not False:
        raise ScenarioError("self-certified empirical admission not permitted")
    try:
        parsed = list(csv.DictReader(io.StringIO(raw.decode("utf-8", errors="strict"))))
    except (ValueError, UnicodeError) as exc:
        raise ScenarioError("invalid CSV") from exc
    if not parsed:
        raise ScenarioError("empty dataset")
    rows = []
    origins = set()
    for record in parsed:
        try:
            origin = (record["region"], record["time"], record["event_id"])
            if not all(origin) or origin in origins:
                raise ScenarioError("empty or duplicated regional event")
            origins.add(origin)
            row = {"region": record["region"], "time": parse_time(record["time"]),
                   "event_id": record["event_id"]}
            for feature in (*BASE, "outcome"):
                val = record[feature]
                if val not in ("0", "1"):
                    raise ScenarioError("binary fields must be exact 0/1")
                row[feature] = int(val)
            for field in AMOUNTS:
                value = record[field]
                if not value.isdigit():
                    raise ScenarioError("amounts must be nonnegative integers")
                row[field] = int(value)
        except (KeyError, AttributeError, TypeError) as exc:
            raise ScenarioError("incomplete scenario row") from exc
        if row["total_loss"] != sum(row[k] for k in ("equity_loss", "lender_loss", "public_loss")):
            raise ScenarioError("loss waterfall does not conserve")
        if row["grid_total"] != sum(row[k] for k in ("grid_ai", "grid_households", "grid_other", "grid_unused")):
            raise ScenarioError("grid capacity does not conserve")
        if row["labour_total"] != sum(row[k] for k in ("labour_housing", "labour_datacentre", "labour_other")):
            raise ScenarioError("skilled labour budget does not conserve")
        rows.append(row)
    return sorted(rows, key=lambda row: (row["time"], row["region"], row["event_id"]))


def features(row: dict, interactive: bool) -> list[int]:
    values = [1] + [row[k] for k in BASE]
    if interactive:
        values.extend(row[a] * row[b] for a, b in INTERACTIONS)
    return values


def sigmoid(x: float) -> float:
    x = min(35.0, max(-35.0, x))
    return 1 / (1 + exp(-x))


def fit(rows: list[dict], interactive: bool) -> list[float]:
    p = len(features(rows[0], interactive))
    beta = [0.] * p
    # Fixed deterministic gradient steps, regularisation and shrinkage.
    for _ in range(750):
        grad = [0.] * p
        for row in rows:
            xx = features(row, interactive)
            error = sigmoid(sum(a*b for a, b in zip(beta, xx))) - row["outcome"]
            for j in range(p):
                grad[j] += error * xx[j]
        n = len(rows)
        for j in range(p):
            penalty = 0.0 if j == 0 else 0.03 * beta[j]
            beta[j] -= 0.6 * (grad[j] / n + penalty)
    return beta


def predict(beta: list[float], row: dict, interactive: bool) -> float:
    return sigmoid(sum(a*b for a, b in zip(beta, features(row, interactive))))


def brier(y: list[int], prob: list[float]) -> float:
    return sum((p - a)**2 for a, p in zip(y, prob)) / len(y)


def logloss(y: list[int], prob: list[float]) -> float:
    eps = 1e-12
    return -sum(a * log(max(eps, p)) + (1-a) * log(max(eps, 1-p))
                for a, p in zip(y, prob)) / len(y)


def validate(raw: bytes, manifest: dict, cutoff: str) -> dict:
    rows = load(raw, manifest)
    boundary = parse_time(cutoff)
    train = [row for row in rows if row["time"] < boundary]
    test = [row for row in rows if row["time"] >= boundary]
    if len(train) < 12 or len(test) < 8:
        raise ScenarioError("insufficient chronological train/holdout observations")
    if len({r["outcome"] for r in train}) < 2:
        raise ScenarioError("training target has no variation")
    if not max(r["time"] for r in train) < min(r["time"] for r in test):
        raise ScenarioError("chronological holdout leakage")
    additive = fit(train, False)
    interactive = fit(train, True)
    y = [r["outcome"] for r in test]
    p0 = [predict(additive, r, False) for r in test]
    p1 = [predict(interactive, r, True) for r in test]
    delta = [(a - yi)**2 - (b - yi)**2 for yi, a, b in zip(y, p0, p1)]
    rng = random.Random(0)
    bootstrap = []
    for _ in range(500):
        bootstrap.append(sum(delta[rng.randrange(len(delta))]
                             for _ in delta) / len(delta))
    bootstrap.sort()
    return {
        "schema": "dashi-cybersyn-scenario-holdout-v1",
        "dataset_id": manifest["dataset_id"],
        "snapshot_sha256": sha256(raw).hexdigest(),
        "split_utc": boundary.isoformat(),
        "training_n": len(train),
        "holdout_n": len(test),
        "train_end_utc": max(r["time"] for r in train).isoformat(),
        "holdout_start_utc": min(r["time"] for r in test).isoformat(),
        "additive_brier": brier(y, p0), "interaction_brier": brier(y, p1),
        "additive_logloss": logloss(y, p0),
        "interaction_logloss": logloss(y, p1),
        "brier_improvement": sum(delta) / len(delta),
        "brier_improvement_bootstrap_95": [bootstrap[12], bootstrap[487]],
        "region_count": len({r["region"] for r in rows}),
        "comparison": "observational time-holdout predictive fit, not causal identification",
        "synthetic_data": manifest["source_layer"] == "synthetic",
        "empirically_admitted": False,
        "world_admitted": False,
        "kernel_proof_certified": False,
        "calibration_status": "unadmitted-reproducible-holdout",
        "conservation_checked": ["loss_waterfall", "grid_capacity", "skilled_labour"],
        "remaining": ["independent source adjudication", "causal confounding review",
                      "multi-region shift and alternative-model validation",
                      "actual world-builder and Agda kernel receipt"]
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("data", type=Path)
    parser.add_argument("manifest", type=Path)
    parser.add_argument("--cutoff", required=True)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = validate(args.data.read_bytes(),
                      json.loads(args.manifest.read_text()), args.cutoff)
    serialized = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.write_text(serialized)
    else:
        print(serialized, end="")


if __name__ == "__main__":
    main()
