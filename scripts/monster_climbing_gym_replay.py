#!/usr/bin/env python3
"""Reproduce the JMD Monster Climbing Gym hole/mutual-pair table.

Diagnostic numerical producer, not a formal zeta-zero certificate.

For a wall N = p**a, the hole lattice is

    h_m = 2*pi*m / (N*log(p)).

The supplied figure is reproduced by restricting holes to the guarded
interval [t_1 + 1, t_849 - 1] and counting deterministic mutual nearest
zero<->hole pairs. Lattice shifts are supported as null controls, but the
source figure's exact random shift list/seed is not known.
"""

from __future__ import annotations

import argparse
import bisect
import json
import math
from pathlib import Path
from typing import Iterable, Sequence

DEFAULT_WALLS = (
    (2, 1), (3, 1), (5, 1), (7, 1), (11, 1),
    (2, 2), (3, 2), (2, 3), (13, 1), (71, 1),
)

SOURCE_COUNTS = {
    (2, 1): (271, 270),
    (3, 1): (644, 581),
    (5, 1): (1571, 820),
    (7, 1): (2660, 845),
    (11, 1): (5151, 849),
    (2, 2): (542, 513),
    (3, 2): (1931, 841),
    (2, 3): (1083, 773),
    (13, 1): (6511, 849),
    (71, 1): (59099, 849),
}


def load_zero_cache(path: Path) -> list[float]:
    payload = json.loads(path.read_text())
    if "ordinates" in payload:
        zeros = [float(x) for x in payload["ordinates"]]
    else:
        scale = int(payload["scale"])
        encoded = [int(x) for x in payload["first_plus_deltas"]]
        zeros = []
        current = 0
        for index, value in enumerate(encoded):
            current = value if index == 0 else current + value
            zeros.append(current / scale)
    if not zeros or any(x <= 0 for x in zeros):
        raise ValueError("zero ordinates must be positive")
    if any(a >= b for a, b in zip(zeros, zeros[1:])):
        raise ValueError("zero ordinates must be strictly increasing")
    return zeros


def generate_zeros(count: int) -> list[float]:
    import mpmath as mp

    return [float(mp.im(mp.zetazero(k))) for k in range(1, count + 1)]


def hole_spacing(prime: int, exponent: int) -> float:
    if prime <= 1 or exponent < 1:
        raise ValueError("prime must exceed 1 and exponent must be positive")
    return 2.0 * math.pi / ((prime ** exponent) * math.log(prime))


def hole_lattice(
    zeros: Sequence[float],
    prime: int,
    exponent: int,
    *,
    guard: float = 1.0,
    lattice_shift: float = 0.0,
) -> list[float]:
    if not zeros:
        raise ValueError("at least one zero ordinate is required")
    lo = zeros[0] + guard
    hi = zeros[-1] - guard
    if lo > hi:
        return []
    spacing = hole_spacing(prime, exponent)
    first_m = math.ceil((lo - lattice_shift) / spacing)
    last_m = math.floor((hi - lattice_shift) / spacing)
    if last_m < first_m:
        return []
    return [spacing * m + lattice_shift for m in range(first_m, last_m + 1)]


def nearest_index(sorted_values: Sequence[float], x: float) -> int:
    if not sorted_values:
        raise ValueError("nearest_index requires a nonempty sequence")
    j = bisect.bisect_left(sorted_values, x)
    candidates = []
    if j:
        candidates.append(j - 1)
    if j < len(sorted_values):
        candidates.append(j)
    return min(candidates, key=lambda k: (abs(sorted_values[k] - x), k))


def mutual_nearest_count(zeros: Sequence[float], holes: Sequence[float]) -> int:
    if not zeros or not holes:
        return 0
    zero_to_hole = [nearest_index(holes, z) for z in zeros]
    hole_to_zero = [nearest_index(zeros, h) for h in holes]
    return sum(
        1 for zero_index, hole_index in enumerate(zero_to_hole)
        if hole_to_zero[hole_index] == zero_index
    )


def replay_wall(
    zeros: Sequence[float],
    *,
    prime: int,
    exponent: int,
    guard: float = 1.0,
    lattice_shift: float = 0.0,
) -> dict[str, object]:
    holes = hole_lattice(
        zeros,
        prime,
        exponent,
        guard=guard,
        lattice_shift=lattice_shift,
    )
    return {
        "prime": prime,
        "exponent": exponent,
        "wall_N": prime ** exponent,
        "guard": guard,
        "lattice_shift": lattice_shift,
        "spacing": hole_spacing(prime, exponent),
        "holes": len(holes),
        "mutual_pairs": mutual_nearest_count(zeros, holes),
    }


def replay_table(
    zeros: Sequence[float],
    *,
    guard: float = 1.0,
    walls: Iterable[tuple[int, int]] = DEFAULT_WALLS,
) -> list[dict[str, object]]:
    return [
        replay_wall(zeros, prime=p, exponent=a, guard=guard)
        for p, a in walls
    ]


def source_count_match(row: dict[str, object]) -> bool:
    key = (int(row["prime"]), int(row["exponent"]))
    return (
        int(row["holes"]),
        int(row["mutual_pairs"]),
    ) == SOURCE_COUNTS.get(key)


def shifted_control_counts(
    zeros: Sequence[float],
    *,
    prime: int,
    exponent: int,
    shifts: Sequence[float],
    guard: float = 1.0,
) -> list[int]:
    return [
        int(replay_wall(
            zeros,
            prime=prime,
            exponent=exponent,
            guard=guard,
            lattice_shift=shift,
        )["mutual_pairs"])
        for shift in shifts
    ]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--zeros-json", type=Path)
    parser.add_argument("--generate-zeros", type=int, default=849)
    parser.add_argument("--guard", type=float, default=1.0)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()

    zeros = (
        load_zero_cache(args.zeros_json)
        if args.zeros_json
        else generate_zeros(args.generate_zeros)
    )
    table = replay_table(zeros, guard=args.guard)
    payload = {
        "contract": "monster_climbing_gym_replay",
        "zero_count": len(zeros),
        "zero_first": zeros[0],
        "zero_last": zeros[-1],
        "guard": args.guard,
        "rows": [
            {**row, "matches_source_counts": source_count_match(row)}
            for row in table
        ],
        "all_source_counts_match": all(source_count_match(row) for row in table),
        "shift_control_boundary": (
            "lattice-shift null supported; source shift list/seed not recovered"
        ),
        "formal_promotion": False,
    }
    text = json.dumps(payload, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.write_text(text)
    else:
        print(text, end="")


if __name__ == "__main__":
    main()
