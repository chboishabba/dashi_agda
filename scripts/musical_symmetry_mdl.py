#!/usr/bin/env python3

from __future__ import annotations

import argparse
import json
import math
import random
from collections import Counter
from dataclasses import asdict, dataclass
from typing import Callable


MODULUS = 12


Melody = tuple[int, ...]


@dataclass
class AttractorSummary:
    melody: list[int]
    symmetry_error: int
    mdl_cost: int
    basin_hits: int
    basin_fraction: float


def canonicalize_transposition(melody: Melody) -> Melody:
    if not melody:
        return melody
    shift = melody[0] % MODULUS
    return tuple((note - shift) % MODULUS for note in melody)


def reverse_symmetry(melody: Melody) -> Melody:
    return tuple(reversed(melody))


def inversion_symmetry(melody: Melody) -> Melody:
    if not melody:
        return melody
    pivot = melody[0] % MODULUS
    return tuple((2 * pivot - note) % MODULUS for note in melody)


def retrograde_inversion_symmetry(melody: Melody) -> Melody:
    return reverse_symmetry(inversion_symmetry(melody))


def symmetry_transform(name: str) -> Callable[[Melody], Melody]:
    options: dict[str, Callable[[Melody], Melody]] = {
        "reverse": reverse_symmetry,
        "inversion": inversion_symmetry,
        "retrograde_inversion": retrograde_inversion_symmetry,
    }
    try:
        return options[name]
    except KeyError as exc:
        raise ValueError(f"unknown symmetry: {name}") from exc


def cyclic_distance(a: int, b: int) -> int:
    diff = (b - a) % MODULUS
    return min(diff, MODULUS - diff)


def signed_cyclic_step(a: int, b: int) -> int:
    diff = (b - a) % MODULUS
    if diff == 0:
        return 0
    if diff <= MODULUS // 2:
        return diff
    return diff - MODULUS


def symmetry_error(melody: Melody, sym: Callable[[Melody], Melody]) -> int:
    partner = sym(melody)
    return sum(cyclic_distance(a, b) for a, b in zip(melody, partner))


def best_period_cost(sequence: tuple[int, ...]) -> tuple[int, int]:
    if not sequence:
        return 0, 0
    best_period = len(sequence)
    best_mismatch = len(sequence)
    for period in range(1, len(sequence) + 1):
        mismatch = sum(1 for i, value in enumerate(sequence) if value != sequence[i % period])
        score = period + mismatch
        if score < best_period + best_mismatch:
            best_period = period
            best_mismatch = mismatch
    return best_period, best_mismatch


def compression_cost(melody: Melody) -> int:
    normalized = canonicalize_transposition(melody)
    if not normalized:
        return 0
    intervals = tuple((normalized[i + 1] - normalized[i]) % MODULUS for i in range(len(normalized) - 1))
    interval_runs = 0
    for left, right in zip(intervals, intervals[1:]):
        if left != right:
            interval_runs += 1
    period, mismatch = best_period_cost(normalized)
    return (
        len(set(normalized))
        + len(set(intervals))
        + interval_runs
        + period
        + mismatch
    )


def flow_step(melody: Melody, sym: Callable[[Melody], Melody], alpha: float) -> Melody:
    target = sym(melody)
    updated = []
    for note, goal in zip(melody, target):
        delta = signed_cyclic_step(note, goal)
        moved = note + int(round(alpha * delta))
        updated.append(moved % MODULUS)
    return tuple(updated)


def biased_accept(candidate: Melody, current: Melody, sym: Callable[[Melody], Melody], beta: float, rng: random.Random) -> Melody:
    if beta <= 0.0:
        return candidate
    current_err = symmetry_error(current, sym)
    candidate_err = symmetry_error(candidate, sym)
    gain = current_err - candidate_err
    if gain >= 0:
        return candidate
    accept_prob = math.exp(beta * gain)
    return candidate if rng.random() < accept_prob else current


def iterate_to_attractor(
    start: Melody,
    *,
    sym: Callable[[Melody], Melody],
    alpha: float,
    mode: str,
    beta: float,
    max_steps: int,
    rng: random.Random,
) -> Melody:
    state = canonicalize_transposition(start)
    seen: dict[Melody, int] = {}
    for _ in range(max_steps):
        if state in seen:
            return state
        seen[state] = 1
        candidate = canonicalize_transposition(flow_step(state, sym, alpha))
        if mode == "symmetry_bias":
            state = canonicalize_transposition(biased_accept(candidate, state, sym, beta, rng))
        elif mode == "mdl":
            if compression_cost(candidate) <= compression_cost(state):
                state = candidate
            else:
                state = state
        else:
            state = candidate
    return state


def random_melody(length: int, rng: random.Random) -> Melody:
    return tuple(rng.randrange(MODULUS) for _ in range(length))


def basin_scan(
    *,
    length: int,
    samples: int,
    alpha: float,
    symmetry_name: str,
    mode: str,
    beta: float,
    max_steps: int,
    seed: int,
) -> dict[str, object]:
    rng = random.Random(seed)
    sym = symmetry_transform(symmetry_name)
    counts: Counter[Melody] = Counter()
    for _ in range(samples):
        start = random_melody(length, rng)
        attractor = iterate_to_attractor(
            start,
            sym=sym,
            alpha=alpha,
            mode=mode,
            beta=beta,
            max_steps=max_steps,
            rng=rng,
        )
        counts[attractor] += 1

    summaries = []
    for melody, hits in counts.most_common():
        summaries.append(
            AttractorSummary(
                melody=list(melody),
                symmetry_error=symmetry_error(melody, sym),
                mdl_cost=compression_cost(melody),
                basin_hits=hits,
                basin_fraction=hits / samples,
            )
        )

    exact_symmetric_basin = sum(item.basin_hits for item in summaries if item.symmetry_error == 0) / samples
    min_mdl = min((item.mdl_cost for item in summaries), default=0)
    low_mdl_basin = sum(item.basin_hits for item in summaries if item.mdl_cost == min_mdl) / samples

    return {
        "experiment": "musical-symmetry-mdl-toy",
        "mode": mode,
        "symmetry": symmetry_name,
        "alpha": alpha,
        "beta": beta,
        "melody_length": length,
        "samples": samples,
        "max_steps": max_steps,
        "seed": seed,
        "notes": [
            "MDL mode uses a simple compression proxy, not a music-theoretic canonical code length.",
            "symmetry_bias mode is retained as a control and should not be read as symmetry emergence.",
            "Attractors are reported after transposition canonicalization."
        ],
        "attractor_count": len(summaries),
        "aggregate_summary": {
            "exact_symmetric_basin_fraction": exact_symmetric_basin,
            "minimum_mdl_cost": min_mdl,
            "minimum_mdl_basin_fraction": low_mdl_basin,
        },
        "top_attractors": [asdict(item) for item in summaries[:10]],
    }


def compare_same_seed(
    *,
    length: int,
    samples: int,
    alpha: float,
    symmetry_name: str,
    beta: float,
    max_steps: int,
    seed: int,
) -> dict[str, object]:
    runs = {}
    for mode in ("symmetry_bias", "mdl"):
        runs[mode] = basin_scan(
            length=length,
            samples=samples,
            alpha=alpha,
            symmetry_name=symmetry_name,
            mode=mode,
            beta=beta,
            max_steps=max_steps,
            seed=seed,
        )
    return {
        "comparison": "same-seed symmetry_bias vs mdl attractor analysis",
        "seed": seed,
        "length": length,
        "samples": samples,
        "alpha": alpha,
        "symmetry": symmetry_name,
        "beta": beta,
        "max_steps": max_steps,
        "runs": runs,
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Toy MDL-based musical symmetry basin scan on (Z12)^n")
    parser.add_argument("--length", type=int, default=8, help="Melody length")
    parser.add_argument("--samples", type=int, default=2000, help="Monte Carlo basin samples")
    parser.add_argument("--alpha", type=float, default=0.5, help="Contraction step size toward symmetry partner")
    parser.add_argument(
        "--symmetry",
        choices=["reverse", "inversion", "retrograde_inversion"],
        default="reverse",
        help="Symmetry transform S",
    )
    parser.add_argument(
        "--mode",
        choices=["plain", "symmetry_bias", "mdl"],
        default="mdl",
        help="Update rule family",
    )
    parser.add_argument("--beta", type=float, default=0.0, help="Legacy symmetry-bias strength")
    parser.add_argument("--max-steps", type=int, default=64, help="Max contraction steps per sample")
    parser.add_argument("--seed", type=int, default=7, help="Random seed")
    parser.add_argument("--output", help="Optional JSON output path")
    parser.add_argument("--compare", action="store_true", help="Compare symmetry_bias and mdl modes on the same seed")
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    if args.compare:
        payload = compare_same_seed(
            length=args.length,
            samples=args.samples,
            alpha=args.alpha,
            symmetry_name=args.symmetry,
            beta=args.beta,
            max_steps=args.max_steps,
            seed=args.seed,
        )
    else:
        payload = basin_scan(
        length=args.length,
        samples=args.samples,
        alpha=args.alpha,
        symmetry_name=args.symmetry,
        mode=args.mode,
        beta=args.beta,
        max_steps=args.max_steps,
        seed=args.seed,
    )
    encoded = json.dumps(payload, indent=2, sort_keys=True) + "\n"
    if args.output:
        with open(args.output, "w", encoding="utf-8") as handle:
            handle.write(encoded)
    else:
        print(encoded)


if __name__ == "__main__":
    main()
