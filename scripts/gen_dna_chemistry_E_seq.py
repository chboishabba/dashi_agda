#!/usr/bin/env python3
"""Generate chemistry-aware DNA sheet observables.

The script keeps three objects separate:
1. exact CAGT input and exact UV chart;
2. four-way coarse/detail lift coefficients and quadratic sheet energies;
3. operational chemistry features used for calibration.

It does not identify the operational scores with microscopic quantum chemistry.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Iterable

import numpy as np

UV = {
    "A": (-1.0, +1.0),
    "C": (+1.0, -1.0),
    "G": (+1.0, +1.0),
    "T": (-1.0, -1.0),
}


def load_fasta(path: Path) -> str:
    chunks: list[str] = []
    with path.open("r", encoding="utf-8") as handle:
        for line in handle:
            line = line.strip().upper()
            if line and not line.startswith(">"):
                chunks.append(line)
    sequence = "".join(chunks)
    invalid = sorted(set(sequence) - set(UV))
    if invalid:
        raise ValueError(f"unsupported FASTA symbols: {invalid}")
    return sequence


def encode_uv(sequence: str) -> np.ndarray:
    return np.asarray([UV[base] for base in sequence], dtype=np.float64).T


def four_way_details(signal: np.ndarray, levels: int) -> tuple[list[np.ndarray], np.ndarray]:
    """Return exact fine-minus-broadcast(coarse) details and final coarse state."""
    current = np.asarray(signal, dtype=np.float64)
    details: list[np.ndarray] = []
    for _ in range(levels):
        if current.size % 4:
            raise ValueError("window length must be divisible by 4**levels")
        coarse = current.reshape(-1, 4).mean(axis=1)
        detail = current - np.repeat(coarse, 4)
        details.append(detail)
        current = coarse
    return details, current


def max_run(sequence: str) -> int:
    if not sequence:
        return 0
    best = run = 1
    for left, right in zip(sequence, sequence[1:]):
        run = run + 1 if left == right else 1
        best = max(best, run)
    return best


def reverse_complement(sequence: str) -> str:
    table = str.maketrans("ACGT", "TGCA")
    return sequence.translate(table)[::-1]


def hairpin_proxy(sequence: str, min_stem: int = 4, max_offset: int = 64) -> int:
    """Bounded exact string correlation proxy, not a thermodynamic ΔG theorem."""
    rc = reverse_complement(sequence)
    score = 0
    n = len(sequence)
    for offset in range(min_stem, min(max_offset, n - min_stem) + 1):
        overlap = n - offset
        if overlap < min_stem:
            continue
        matches = sum(a == b for a, b in zip(sequence[:overlap], rc[offset : offset + overlap]))
        score = max(score, matches)
    return score


def chemistry_features(sequence: str, forbidden: Iterable[str]) -> dict[str, float | int]:
    gc = sum(base in "GC" for base in sequence)
    forbidden_count = sum(sequence.count(motif) for motif in forbidden)
    dinucleotide_gc = sum(a in "GC" and b in "GC" for a, b in zip(sequence, sequence[1:]))
    return {
        "length": len(sequence),
        "gc_count": gc,
        "gc_fraction": gc / len(sequence) if sequence else 0.0,
        "max_run": max_run(sequence),
        "forbidden_motif_count": forbidden_count,
        "nearest_neighbour_gc_proxy": dinucleotide_gc,
        "hairpin_correlation_proxy": hairpin_proxy(sequence),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--fasta", required=True, type=Path)
    parser.add_argument("--window", type=int, default=256)
    parser.add_argument("--step", type=int, default=64)
    parser.add_argument("--levels", type=int, default=4)
    parser.add_argument("--forbidden", nargs="*", default=[])
    parser.add_argument("--out", required=True, type=Path)
    parser.add_argument("--features-out", type=Path)
    parser.add_argument("--cross-rank", action="store_true")
    args = parser.parse_args()

    if args.window <= 0 or args.step <= 0:
        raise ValueError("window and step must be positive")
    if args.window % (4**args.levels):
        raise ValueError("window must be divisible by 4**levels")

    sequence = load_fasta(args.fasta)
    if len(sequence) < args.window:
        raise ValueError("sequence is shorter than the requested window")

    starts = range(0, len(sequence) - args.window + 1, args.step)
    rows: list[list[float]] = []
    feature_rows: list[dict[str, float | int]] = []

    for start in starts:
        window = sequence[start : start + args.window]
        channels = encode_uv(window)
        channel_energies: list[float] = []
        channel_details: list[list[np.ndarray]] = []
        for channel in channels:
            details, _ = four_way_details(channel, args.levels)
            channel_details.append(details)
            channel_energies.extend(float(np.mean(detail * detail)) for detail in details)

        if args.cross_rank:
            for channel_details_one in channel_details:
                for fine, coarse in zip(channel_details_one, channel_details_one[1:]):
                    expanded = np.repeat(coarse, fine.size // coarse.size)
                    channel_energies.append(float(np.mean(fine * expanded)))

        rows.append(channel_energies)
        feature_rows.append(chemistry_features(window, args.forbidden))

    energy = np.asarray(rows, dtype=np.float64)
    means = energy.mean(axis=0, keepdims=True)
    normalized = np.divide(energy, means, out=np.zeros_like(energy), where=means != 0)

    args.out.parent.mkdir(parents=True, exist_ok=True)
    np.save(args.out, normalized.astype(np.float32))

    features_out = args.features_out or args.out.with_suffix(".chemistry.json")
    features_out.parent.mkdir(parents=True, exist_ok=True)
    features_out.write_text(json.dumps(feature_rows, indent=2), encoding="utf-8")

    print(f"wrote {args.out}: shape={normalized.shape}")
    print(f"wrote {features_out}: windows={len(feature_rows)}")


if __name__ == "__main__":
    main()
