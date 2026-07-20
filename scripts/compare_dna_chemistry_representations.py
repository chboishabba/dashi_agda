#!/usr/bin/env python3
"""Compare DNA representations against externally supplied chemistry labels.

Input NPZ contract:
  raw:       [N, F_raw]
  one_hot:   [N, F_one_hot]
  uv_sheet:  [N, F_uv]
  trit_sheet:[N, F_trit]
  chemistry: [N, F_chem]
  labels:    [N] binary admissibility labels

The harness uses deterministic ridge classification and reports balanced
accuracy and false-acceptance rate.  It supplies no chemistry labels itself.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

import numpy as np

REPRESENTATIONS = ("raw", "one_hot", "uv_sheet", "trit_sheet", "chemistry")


def standardize(train: np.ndarray, test: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    mean = train.mean(axis=0, keepdims=True)
    std = train.std(axis=0, keepdims=True)
    std[std == 0] = 1.0
    return (train - mean) / std, (test - mean) / std


def fit_ridge(x: np.ndarray, y: np.ndarray, lam: float) -> np.ndarray:
    x1 = np.column_stack([np.ones(len(x)), x])
    identity = np.eye(x1.shape[1])
    identity[0, 0] = 0.0
    return np.linalg.solve(x1.T @ x1 + lam * identity, x1.T @ y)


def predict(x: np.ndarray, weights: np.ndarray) -> np.ndarray:
    x1 = np.column_stack([np.ones(len(x)), x])
    return (x1 @ weights >= 0.5).astype(np.int64)


def metrics(y: np.ndarray, pred: np.ndarray) -> dict[str, float]:
    positive = y == 1
    negative = ~positive
    tpr = float((pred[positive] == 1).mean()) if positive.any() else 0.0
    tnr = float((pred[negative] == 0).mean()) if negative.any() else 0.0
    false_acceptance = float((pred[negative] == 1).mean()) if negative.any() else 0.0
    return {
        "balanced_accuracy": 0.5 * (tpr + tnr),
        "false_acceptance_rate": false_acceptance,
        "sensitivity": tpr,
        "specificity": tnr,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--dataset", required=True, type=Path)
    parser.add_argument("--out", required=True, type=Path)
    parser.add_argument("--train-fraction", type=float, default=0.8)
    parser.add_argument("--ridge", type=float, default=1.0)
    args = parser.parse_args()

    data = np.load(args.dataset)
    missing = [name for name in (*REPRESENTATIONS, "labels") if name not in data]
    if missing:
        raise ValueError(f"dataset is missing arrays: {missing}")

    labels = np.asarray(data["labels"], dtype=np.int64)
    n = len(labels)
    split = int(n * args.train_fraction)
    if split <= 0 or split >= n:
        raise ValueError("train-fraction must leave nonempty train and test sets")

    report: dict[str, dict[str, float]] = {}
    for name in REPRESENTATIONS:
        features = np.asarray(data[name], dtype=np.float64)
        if len(features) != n:
            raise ValueError(f"{name} row count differs from labels")
        train_x, test_x = standardize(features[:split], features[split:])
        weights = fit_ridge(train_x, labels[:split].astype(np.float64), args.ridge)
        report[name] = metrics(labels[split:], predict(test_x, weights))

    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(report, indent=2), encoding="utf-8")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
