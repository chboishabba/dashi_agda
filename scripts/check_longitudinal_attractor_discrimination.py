#!/usr/bin/env python3
"""Held-out longitudinal source-specific model discrimination, not data fabrication.

Each row is a measured specimen/time point. The two supplied model probabilities
must be predictions made without fitting to the held-out experiment IDs. Only
the FINAL observed time point per specimen is scored; experiment IDs are the
bootstrap units, preventing repeated-timepoint pseudoreplication.
No original prospective planarian measurements are bundled here.
"""
from __future__ import annotations

import argparse
import csv
import hashlib
import json
import math
import random
import tempfile
from collections import defaultdict
from pathlib import Path

COLUMNS = (
    "source_id", "original_source_sha256", "experiment_id", "specimen_id",
    "split", "intervention_trace", "time_s", "observed_target",
    "model_a_probability", "model_b_probability",
)


def _probability(token: str) -> float:
    value = float(token)
    if not math.isfinite(value) or not (0 < value < 1):
        raise ValueError("model probability must be finite and strictly in (0,1)")
    return value


def load_original_rows(path: Path):
    raw = path.read_bytes()
    with path.open(newline="", encoding="utf-8") as handle:
        reader = csv.DictReader(handle)
        if not set(COLUMNS).issubset(reader.fieldnames or []):
            raise ValueError("missing longitudinal columns")
        data = list(reader)
    if not data:
        raise ValueError("no measured longitudinal rows")
    groups, specimens = {}, defaultdict(list)
    source_keys = set()
    seen = set()
    for row in data:
        source = row["source_id"].strip()
        sha = row["original_source_sha256"].strip().lower()
        experiment = row["experiment_id"].strip()
        specimen = row["specimen_id"].strip()
        split = row["split"].strip().lower()
        trace = row["intervention_trace"].strip()
        if not source or not experiment or not specimen or not trace:
            raise ValueError("missing original source, experiment, specimen or trace")
        if len(sha) != 64 or any(c not in "0123456789abcdef" for c in sha):
            raise ValueError("malformed original source digest")
        if split not in {"train", "validation", "test"}:
            raise ValueError("split must be train, validation or test")
        source_keys.add((source, sha))
        key = (source, experiment, specimen)
        subject_meta = (source, sha, experiment, split, trace)
        t = float(row["time_s"])
        if not math.isfinite(t) or t < 0:
            raise ValueError("time_s must be nonnegative and finite")
        if (key, t) in seen:
            raise ValueError("duplicate specimen/time measurement")
        seen.add((key, t))
        if row["observed_target"] not in ("0", "1"):
            raise ValueError("binary target observation required")
        y = int(row["observed_target"])
        a = _probability(row["model_a_probability"])
        b = _probability(row["model_b_probability"])
        if experiment in groups and groups[experiment] != (source, sha, split):
            raise ValueError("experiment spans sources or evaluation splits")
        groups[experiment] = (source, sha, split)
        if specimens[key] and specimens[key][0][0] != subject_meta:
            raise ValueError("specimen changes provenance, intervention or split")
        specimens[key].append((subject_meta, t, y, a, b))
    if len(source_keys) != 1:
        raise ValueError("mixed original sources cannot be pooled as one assay")

    terminal = []
    for key, observations in specimens.items():
        observations.sort(key=lambda record: record[1])
        if len(observations) < 2 or observations[0][1] >= observations[-1][1]:
            raise ValueError("each specimen requires two distinct longitudinal times")
        metadata, t, y, a, b = observations[-1]
        terminal.append((metadata[2], metadata[3], y, a, b))
    if len({exp for exp, split, *_ in terminal if split == "test"}) < 2:
        raise ValueError("need two or more independent held-out test experiments")
    return terminal, hashlib.sha256(raw).hexdigest(), sorted(source_keys)[0], len(data)


def logloss(y: int, p: float) -> float:
    return -(math.log(p) if y else math.log1p(-p))


def delta_brier(y: int, p_a: float, p_b: float) -> float:
    return (p_b-y)**2 - (p_a-y)**2


def evaluate(path: Path, draws: int = 1000, seed: int = 1471):
    if draws < 100:
        raise ValueError("at least 100 bootstrap draws required")
    rows, sha, source, n_times = load_original_rows(path)
    test = [r for r in rows if r[1] == "test"]
    experiments = defaultdict(list)
    for experiment, split, y, a, b in test:
        experiments[experiment].append((y, a, b))
    if len(experiments) < 2:
        raise ValueError("held-out experiment groups missing")
    def scores(experiment_ids):
        obs = [row for ident in experiment_ids for row in experiments[ident]]
        improvement = [logloss(y, b) - logloss(y, a) for y, a, b in obs]
        brier = [delta_brier(y, a, b) for y, a, b in obs]
        return sum(improvement) / len(obs), sum(brier) / len(obs)
    ids = sorted(experiments)
    observed_logloss, observed_brier = scores(ids)
    rng = random.Random(seed)
    sampled = sorted(
        scores([rng.choice(ids) for _ in ids])[0] for _ in range(draws)
    )
    lo = sampled[int(0.025 * draws)]
    hi = sampled[min(draws-1, math.ceil(0.975 * draws)-1)]
    return {
        "status": "heldout-longitudinal-model-comparison-not-biological-validation",
        "original_source_id": source[0],
        "declared_original_source_sha256": source[1],
        "observed_csv_sha256": sha,
        "independent_source_digest_verified_externally": False,
        "measured_timepoint_rows": n_times,
        "distinct_specimens": len(rows),
        "heldout_specimens": len(test),
        "heldout_experiment_groups": len(experiments),
        "test_mean_logloss_improvement_a_over_b": observed_logloss,
        "test_mean_brier_improvement_a_over_b": observed_brier,
        "cluster_bootstrap_logloss_improvement_95": [lo, hi],
        "cluster_bootstrap_seed": seed,
        "cluster_bootstrap_draws": draws,
        "only_final_endpoint_per_specimen_scored": True,
        "test_experiment_ids_never_used_to_fit_models_by_this_script": True,
        "model_predictions_independently_pre_registered_verified": False,
        "wetlab_independent_replication_verified": False,
        "pnf_mutation_performed": False,
    }


def self_test():
    with tempfile.TemporaryDirectory() as dirname:
        path = Path(dirname) / "synthetic-not-original.csv"
        with path.open("w", newline="") as stream:
            writer = csv.writer(stream)
            writer.writerow(COLUMNS)
            for exp in range(6):
                split = "train" if exp < 2 else ("validation" if exp < 4 else "test")
                for specimen in range(3):
                    y = (exp + specimen) % 2
                    for time in (0, 10, 20):
                        writer.writerow((
                            "SYNTHETIC:NO-EXPERIMENT", "0"*64, str(exp),
                            f"specimen-{exp}-{specimen}", split, "wound,signal",
                            time, y, .85 if y else .15, .45 if y else .55,
                        ))
        result = evaluate(path, draws=200)
        assert result["heldout_experiment_groups"] == 2
        assert result["heldout_specimens"] == 6
        assert result["measured_timepoint_rows"] == 54
        assert result["test_mean_logloss_improvement_a_over_b"] > 0
        # Deliberate held-out leakage must fail closed.
        with path.open("a") as stream:
            stream.write("SYNTHETIC:NO-EXPERIMENT," + "0"*64 +
                         ",4,specimen-4-0,train,wound,signal,30,1,.9,.3\n")
        try:
            load_original_rows(path)
        except ValueError:
            pass
        else:
            raise AssertionError("mixed split for the same experiment admitted")
        print("PASS: independent experiment split, longitudinal scoring, cluster bootstrap")
        print("SYNTHETIC ONLY; no real organismal attractor result")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--assay", type=Path)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--bootstrap", type=int, default=1000)
    parser.add_argument("--seed", type=int, default=1471)
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    if args.self_test:
        self_test()
        return
    if args.assay is None or args.output is None:
        parser.error("--assay and --output required unless --self-test")
    report = evaluate(args.assay, args.bootstrap, args.seed)
    args.output.write_text(json.dumps(report, sort_keys=True, indent=2) + "\n")
    print(json.dumps(report, sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
