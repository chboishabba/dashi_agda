#!/usr/bin/env python3
"""Original dmsC replicate-range sensitivity at measured Hamming-one edges.

This is descriptive deterministic sample-level analysis.  The thresholds
are illustrative assay-scale tolerances, NOT calibrated equivalence margins.
"All within" means every *observed* replicate combination lies within a
declared tolerance; it does not prove future equivalence or a neutral basin.
"""
import argparse
import csv
import hashlib
import io
import json
import math
from pathlib import Path

BLOB = "151cd87272cbdd6bcc2b1e70bdfd2a4ea2933d2c"
N = 4 ** 9
ALPHABET = {"A": 0, "C": 1, "G": 2, "U": 3}
COLUMNS = ("dmsC.1", "dmsC.2", "dmsC.3")
THRESHOLDS = (0.05, 0.1, 0.2)


def git_blob_sha(raw):
    prefix = f"blob {len(raw)}\0".encode("ascii")
    return hashlib.sha1(prefix + raw).hexdigest()


def parse_original(raw, enforce_blob=True):
    blob = git_blob_sha(raw)
    if enforce_blob and blob != BLOB:
        raise ValueError(f"original source blob mismatch: expected {BLOB}, got {blob}")
    means = [None] * N
    lower = [None] * N
    upper = [None] * N
    counts = [0] * N
    reader = csv.DictReader(io.StringIO(raw.decode("utf-8")))
    if not {"Genotype", *COLUMNS}.issubset(reader.fieldnames or []):
        raise ValueError("required original measured dmsC columns missing")
    observed = 0
    for row in reader:
        sequence = (row["Genotype"] or "").strip().upper()
        if len(sequence) != 9 or any(base not in ALPHABET for base in sequence):
            raise ValueError("invalid RNA 9-mer in source")
        idx = 0
        for base in sequence:
            idx = 4 * idx + ALPHABET[base]
        if counts[idx] != 0 or means[idx] is not None:
            raise ValueError("repeated source 9-mer genotype")
        values = []
        for col in COLUMNS:
            token = (row[col] or "").strip()
            if token and token.lower() not in ("nan", "na", "null"):
                value = float(token)
                if not math.isfinite(value):
                    raise ValueError("nonfinite measured replicate")
                values.append(value)
        if values:
            observed += 1
            means[idx] = sum(values) / len(values)
            lower[idx] = min(values)
            upper[idx] = max(values)
            counts[idx] = len(values)
        else:
            # Zero-replicate genotypes still have to be unique.
            counts[idx] = -1
    # Negative one distinguishes source-present but unmeasured genotypes.
    return means, lower, upper, counts, {"source_git_blob": blob,
        "source_sha256": hashlib.sha256(raw).hexdigest(),
        "measured_genotypes": observed}


def census(means, low, high, replicates, thresholds=THRESHOLDS):
    eps = tuple(sorted(set(thresholds)))
    if not eps or any(not math.isfinite(x) or x < 0 for x in eps):
        raise ValueError("nonnegative finite thresholds required")
    rows = [{"epsilon": x, "mean_within": 0,
             "all_observed_replicate_pairs_within": 0,
             "all_observed_replicate_pairs_beyond": 0,
             "mixed_observed_replicate_ranges": 0,
             "insufficient_replicate_edges": 0,
             "edges_with_two_or_more_replicates_per_genotype": 0} for x in eps]
    possible = 0
    for i, a in enumerate(means):
        if a is None:
            continue
        power = 1
        for _ in range(9):
            base = (i // power) % 4
            for alternative in range(base + 1, 4):
                j = i + (alternative-base) * power
                b = means[j]
                if b is None:
                    continue
                possible += 1
                difference = abs(a-b)
                # Maximum absolute difference across every observed pair.
                maxdiff = max(abs(low[i]-high[j]), abs(high[i]-low[j]))
                # Minimum observed-range distance: 0 when ranges overlap.
                mindiff = max(0., low[i]-high[j], low[j]-high[i])
                enough = replicates[i] >= 2 and replicates[j] >= 2
                for entry in rows:
                    tol = entry["epsilon"]
                    if difference <= tol:
                        entry["mean_within"] += 1
                    if not enough:
                        entry["insufficient_replicate_edges"] += 1
                    else:
                        entry["edges_with_two_or_more_replicates_per_genotype"] += 1
                        if maxdiff <= tol:
                            entry["all_observed_replicate_pairs_within"] += 1
                        elif mindiff > tol:
                            entry["all_observed_replicate_pairs_beyond"] += 1
                        else:
                            entry["mixed_observed_replicate_ranges"] += 1
            power *= 4
    for entry in rows:
        assert entry["insufficient_replicate_edges"] + entry[
            "edges_with_two_or_more_replicates_per_genotype"] == possible
        assert (entry["all_observed_replicate_pairs_within"]
                + entry["all_observed_replicate_pairs_beyond"]
                + entry["mixed_observed_replicate_ranges"]
                == entry["edges_with_two_or_more_replicates_per_genotype"])
    return {"measured_hamming_one_edges": possible, "threshold_results": rows,
        "tolerance_calibrated_by_source": False,
        "future_equivalence_or_attractor_basin_established": False,
        "pnf_mutation_performed": False}


def self_test():
    import csv
    stream = io.StringIO()
    writer = csv.writer(stream)
    writer.writerow(("Genotype", *COLUMNS))
    writer.writerow(("AAAAAAAAA", "0.10", "0.20", "0.15"))
    writer.writerow(("AAAAAAAAC", "0.12", "0.18", "0.15"))
    writer.writerow(("AAAAAAAAG", "0.80", "0.90", ""))
    means, low, high, rep, source = parse_original(
        stream.getvalue().encode("utf-8"), enforce_blob=False)
    result = census(means, low, high, rep, (0.10, 0.20))
    assert result["measured_hamming_one_edges"] == 3
    assert result["threshold_results"][0]["all_observed_replicate_pairs_within"] == 1
    assert result["threshold_results"][0]["all_observed_replicate_pairs_beyond"] == 2
    assert result["threshold_results"][0]["mixed_observed_replicate_ranges"] == 0
    assert source["measured_genotypes"] == 3
    print("PASS: measured-only Hamming-one source, pairwise replicate-range partition")
    print("SELF-TEST SYNTHETIC; empirical receipt requires exact pinned Git blob")


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--original-csv", type=Path)
    p.add_argument("--receipt", type=Path)
    p.add_argument("--self-test", action="store_true")
    args = p.parse_args()
    if args.self_test:
        self_test()
        return
    if args.original_csv is None or args.receipt is None:
        p.error("--original-csv and --receipt are required")
    means, low, high, reps, source = parse_original(
        args.original_csv.read_bytes())
    result = {**source, **census(means, low, high, reps)}
    args.receipt.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
