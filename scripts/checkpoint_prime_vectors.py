#!/usr/bin/env python3
"""Encode training checkpoints as prime-exponent vectors and Gödel integers."""

from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from math import floor, log1p
from pathlib import Path
from typing import Iterable, Sequence

import pandas as pd


SSP_PRIMES: tuple[int, ...] = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71)


@dataclass(frozen=True)
class PrimeFeature:
    prime: int
    column: str
    scale: float
    cap: int = 12


DEFAULT_FEATURES: tuple[PrimeFeature, ...] = (
    PrimeFeature(2, "train_loss", 10.0),
    PrimeFeature(3, "val_loss", 10.0),
    PrimeFeature(5, "sr_block0", 1.0),
    PrimeFeature(7, "sr_block5", 1.0),
    PrimeFeature(11, "sr_block11", 1.0),
    PrimeFeature(13, "cn_block0", 0.01),
    PrimeFeature(17, "cn_block5", 0.01),
    PrimeFeature(19, "cn_block11", 0.01),
    PrimeFeature(23, "spike_amp", 10.0),
    PrimeFeature(29, "spike_interval", 0.1),
    PrimeFeature(31, "peak_width", 10.0),
    PrimeFeature(41, "coherence_score", 10.0),
    PrimeFeature(47, "horror_score", 10.0),
    PrimeFeature(59, "safe_score", 10.0),
    PrimeFeature(71, "phase_id", 1.0, cap=256),
)


def bucket(value: float, *, scale: float, cap: int) -> int:
    if value <= 0:
        return 0
    return min(cap, int(floor(log1p(scale * value))))


def encode_row(row: pd.Series, features: Sequence[PrimeFeature]) -> dict[int, int]:
    exp_map: dict[int, int] = {}
    for feature in features:
        value = row.get(feature.column, 0.0)
        if feature.column == "phase_id":
            exp_map[feature.prime] = int(value)
            continue
        exp_map[feature.prime] = bucket(float(value), scale=feature.scale, cap=feature.cap)
    return exp_map


def godel_integer(exp_map: dict[int, int]) -> str:
    n = 1
    for prime in SSP_PRIMES:
        exponent = int(exp_map.get(prime, 0))
        if exponent:
            n *= prime**exponent
    return str(n)


def parse_args() -> argparse.Namespace:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--csv", required=True, help="Input checkpoint CSV")
    ap.add_argument("--step", default="step", help="Step column")
    ap.add_argument("--out", default="checkpoint_prime_vectors.csv", help="Output CSV")
    ap.add_argument(
        "--include-godel",
        action="store_true",
        help="Add a literal Gödel integer column as a decimal string",
    )
    ap.add_argument(
        "--pretty-json",
        action="store_true",
        help="Emit a companion JSON summary alongside the CSV",
    )
    return ap.parse_args()


def main() -> int:
    args = parse_args()
    df = pd.read_csv(args.csv)
    if args.step not in df.columns:
        raise ValueError(f"Missing step column: {args.step!r}")

    features = [feature for feature in DEFAULT_FEATURES if feature.column in df.columns]
    if not features:
        raise ValueError("No default feature columns were found in the input CSV")

    rows: list[dict[str, object]] = []
    for _, row in df.sort_values(args.step).iterrows():
        exp_map = encode_row(row, features)
        record: dict[str, object] = {
            args.step: row[args.step],
            "prime_vector": json.dumps({str(p): int(exp_map.get(p, 0)) for p in SSP_PRIMES}, sort_keys=True),
        }
        for prime in SSP_PRIMES:
            record[f"e_{prime}"] = int(exp_map.get(prime, 0))
        if args.include_godel:
            record["godel_integer"] = godel_integer(exp_map)
        rows.append(record)

    out_df = pd.DataFrame(rows)
    out_df.to_csv(args.out, index=False)

    summary = {
        "rows": int(len(out_df)),
        "features_used": [f"{feature.prime}:{feature.column}" for feature in features],
        "canonical_primes": list(SSP_PRIMES),
        "output": args.out,
    }

    print(f"[ok] wrote: {args.out}")
    print(f"[info] rows: {summary['rows']}")
    print(f"[info] features used: {summary['features_used']}")
    if args.pretty_json:
        print(json.dumps(summary, indent=2, sort_keys=True))
    else:
        print(json.dumps(summary, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
