"""Train-only, capacity-matched quotient linear probes for frozen visual features.

This is a *surrogate information-retention diagnostic* for measured BOLD-like
features; it is not a reimplementation of Brain-IT's V2C/BIT transformer.
All source labels, features and partitions must be externally admitted.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import numpy as np

from inventory import digest


def pool_by_cluster(x: np.ndarray, labels: np.ndarray) -> np.ndarray:
    x = np.asarray(x, dtype=np.float64)
    labels = np.asarray(labels)
    if x.ndim != 2 or labels.ndim != 1 or x.shape[1] != len(labels):
        raise ValueError("Require voxel matrix N,V and one label per voxel")
    if not np.issubdtype(labels.dtype, np.integer) or (labels < 0).any():
        raise ValueError("Only nonnegative integer cluster labels allowed")
    unique, mapped = np.unique(labels, return_inverse=True)
    if not 2 <= len(unique) <= x.shape[1]:
        raise ValueError("Require at least two nonempty clusters")
    if not np.isfinite(x).all():
        raise ValueError("Nonfinite voxel samples")
    # Exact per-cluster mean pooling, independently named rather than calling
    # this Brain-IT's GMM-aware voxel embedding stage.
    indicator = np.eye(len(unique), dtype=np.float64)[mapped]
    sizes = indicator.sum(axis=0)
    return (x @ indicator) / sizes


def permuted_partition(labels: np.ndarray, seed: int) -> np.ndarray:
    """Random voxel reassignment preserving every cluster's exact size."""
    rng = np.random.default_rng(seed)
    return np.asarray(labels)[rng.permutation(len(labels))]


def ridge_probe(x_train: np.ndarray, y_train: np.ndarray,
                x_test: np.ndarray, y_test: np.ndarray,
                alpha: float = 1.0) -> dict:
    if alpha <= 0 or not np.isfinite(alpha):
        raise ValueError("Strictly positive finite ridge alpha required")
    xs = [np.asarray(x, dtype=np.float64) for x in
          (x_train, y_train, x_test, y_test)]
    a, b, c, d = xs
    if any(x.ndim != 2 or not np.isfinite(x).all() for x in xs):
        raise ValueError("Finite 2D arrays required")
    if len(a) != len(b) or len(c) != len(d) or a.shape[1] != c.shape[1] or b.shape[1] != d.shape[1]:
        raise ValueError("Training/test rows or dimensions mismatch")
    if len(a) < 3 or len(c) < 2:
        raise ValueError("Insufficient train/test samples")
    xm = a.mean(axis=0)
    xsdev = a.std(axis=0)
    xsdev[xsdev == 0] = 1
    train = (a - xm) / xsdev
    test = (c - xm) / xsdev
    ym = b.mean(axis=0)
    yc = b - ym
    # Dual ridge works when feature dimension exceeds sample count.
    if train.shape[1] > len(train):
        w = train.T @ np.linalg.solve(
            train @ train.T + alpha * np.eye(len(train)), yc)
    else:
        w = np.linalg.solve(
            train.T @ train + alpha * np.eye(train.shape[1]),
            train.T @ yc)
    pred = test @ w + ym
    baseline = np.broadcast_to(ym, d.shape)
    mse = float(np.mean((pred - d)**2))
    base_mse = float(np.mean((baseline - d)**2))
    result = {
        "test_mse": mse, "mean_only_test_mse": base_mse,
        "relative_improvement_over_train_mean":
            float(1 - mse / base_mse) if base_mse > 0 else None,
        "n_train": len(a), "n_test": len(c),
        "n_features": a.shape[1], "target_dimension": b.shape[1],
        "alpha": alpha, "train_only_normalisation": True,
    }
    return result


def run_probe(train_x: np.ndarray, test_x: np.ndarray, train_y: np.ndarray,
              test_y: np.ndarray, train_ids: list, test_ids: list,
              labels: np.ndarray, alpha: float, seeds: list[int]) -> dict:
    if len(set(train_ids)) != len(train_ids) or len(set(test_ids)) != len(test_ids):
        raise ValueError("Repeated stimulus identities require group-level splits")
    if set(train_ids).intersection(test_ids):
        raise ValueError("Stimulus leakage: train/test IDs overlap")
    if len(train_ids) != len(train_x) or len(test_ids) != len(test_x):
        raise ValueError("Train/test sample identity and feature rows misaligned")
    baseline = ridge_probe(pool_by_cluster(train_x, labels), train_y,
                           pool_by_cluster(test_x, labels), test_y, alpha)
    controls = []
    for seed in seeds:
        shuffled_labels = permuted_partition(labels, seed)
        controls.append({"seed": seed, **ridge_probe(
            pool_by_cluster(train_x, shuffled_labels), train_y,
            pool_by_cluster(test_x, shuffled_labels), test_y, alpha)})
    return {
        "schema": "brainit-surrogate-probe-v1",
        "surrogate_not_trained_BrainIT": True,
        "claim": "Held-out linear recoverability of a declared target representation",
        "functional_or_source_partition": baseline,
        "cluster_size_matched_random_controls": controls,
        "partition_cluster_count": int(len(np.unique(labels))),
        "n_random_controls": len(controls),
        "all_split_ids_explicit": True,
        "neural_causation_or_model_improvement_proved": False,
    }


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__)
    for name in ("train-x", "test-x", "train-y", "test-y", "labels"):
        ap.add_argument("--" + name, type=Path, required=True)
    ap.add_argument("--train-ids", type=Path, required=True,
                    help="JSON array of unique stimulus IDs")
    ap.add_argument("--test-ids", type=Path, required=True)
    ap.add_argument("--source-of-visual-features", type=str, required=True)
    ap.add_argument("--partition-provenance", type=str, required=True)
    ap.add_argument("--alpha", type=float, default=1.0)
    ap.add_argument("--random-seeds", type=int, nargs="+", default=[1, 2, 3, 4, 5])
    ap.add_argument("--out", type=Path, required=True)
    args = ap.parse_args(argv)
    files = {name.replace("-", "_"): getattr(args, name.replace("-", "_"))
             for name in ("train-x", "test-x", "train-y", "test-y", "labels")}
    arrays = {k: np.load(v, allow_pickle=False) for k, v in files.items()}
    ids_train = json.loads(args.train_ids.read_text())
    ids_test = json.loads(args.test_ids.read_text())
    report = run_probe(arrays["train_x"], arrays["test_x"],
                       arrays["train_y"], arrays["test_y"],
                       ids_train, ids_test, arrays["labels"], args.alpha,
                       args.random_seeds)
    report["provenance"] = {
        "target_feature_encoder": args.source_of_visual_features,
        "cluster_partition": args.partition_provenance,
        "artifacts_sha256": {k: digest(v) for k,v in files.items()},
        "train_ids_sha256": digest(args.train_ids),
        "test_ids_sha256": digest(args.test_ids)}
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(json.dumps(report["functional_or_source_partition"], indent=2))


if __name__ == "__main__":
    main()
