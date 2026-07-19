#!/usr/bin/env python3
"""Ternary Life as a spatial three-strategy game.

States are {-1, 0, +1}.  The default evolving regime is B34/S234:

* inactive cells enter on 3 or 4 active neighbours;
* active cells survive on 2, 3, or 4 active neighbours;
* polarity follows the local +/- majority;
* exact ties are resolved by a deterministic, seedable tie policy.

The module also supplies:

* rollout and Hamming-divergence diagnostics;
* a tabular mixture-of-experts learner, one expert per centre state;
* a small motif census for fixed points and short-period oscillators.

The learner is intentionally interpretable: it recovers a local transition
lookup table over (centre, positive count, negative count), rather than hiding
the rule in a large neural network.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Iterable, Literal

import argparse
import json
import numpy as np

TieMode = Literal["hold", "positive", "negative", "checker", "hash"]


@dataclass(frozen=True)
class Rule:
    birth: tuple[int, ...] = (3, 4)
    survive: tuple[int, ...] = (2, 3, 4)
    tie_mode: TieMode = "hash"
    field_alpha: float = 0.0


def neighbour_counts(grid: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    """Return (+1 count, -1 count) for each Moore neighbourhood."""
    if grid.ndim != 2:
        raise ValueError(f"grid must be 2-D, got shape {grid.shape}")
    if not np.isin(grid, (-1, 0, 1)).all():
        raise ValueError("grid values must lie in {-1, 0, +1}")

    padded = np.pad(grid.astype(np.int8, copy=False), 1, mode="wrap")
    neighbours = np.stack(
        [
            padded[:-2, :-2], padded[:-2, 1:-1], padded[:-2, 2:],
            padded[1:-1, :-2], padded[1:-1, 2:],
            padded[2:, :-2], padded[2:, 1:-1], padded[2:, 2:],
        ],
        axis=0,
    )
    return (neighbours == 1).sum(axis=0), (neighbours == -1).sum(axis=0)


def tie_field(shape: tuple[int, int], mode: TieMode, generation: int) -> np.ndarray:
    """Produce a deterministic tie decision in {-1, 0, +1}."""
    if mode == "hold":
        return np.zeros(shape, dtype=np.int8)
    if mode == "positive":
        return np.ones(shape, dtype=np.int8)
    if mode == "negative":
        return -np.ones(shape, dtype=np.int8)

    rows, cols = np.indices(shape, dtype=np.int64)
    if mode == "checker":
        return np.where((rows + cols + generation) % 2 == 0, 1, -1).astype(np.int8)
    if mode == "hash":
        # Coordinate/generation hash: deterministic and reproducible, but locally
        # irregular enough to prevent a global directional bias.
        h = rows * 73_856_093 ^ cols * 19_349_663 ^ generation * 83_492_791
        return np.where((h & 1) == 0, 1, -1).astype(np.int8)
    raise ValueError(f"unknown tie mode: {mode}")


def step(grid: np.ndarray, rule: Rule = Rule(), generation: int = 0) -> np.ndarray:
    """Apply one synchronous ternary-Life/game update."""
    pos, neg = neighbour_counts(grid)
    active = pos + neg
    signed = pos - neg

    # field_alpha changes polarity competition, not population viability.
    # alpha=0 is pure count-majority; positive alpha amplifies territorial bias.
    polarity_score = signed.astype(np.float64) * (1.0 + rule.field_alpha)
    polarity = np.sign(polarity_score).astype(np.int8)
    ties = polarity == 0
    polarity[ties] = tie_field(grid.shape, rule.tie_mode, generation)[ties]

    out = np.zeros_like(grid, dtype=np.int8)
    born = (grid == 0) & np.isin(active, rule.birth)
    survive = (grid != 0) & np.isin(active, rule.survive)
    out[born] = polarity[born]
    out[survive] = grid[survive]
    return out


def rollout(grid: np.ndarray, steps: int, rule: Rule = Rule()) -> np.ndarray:
    history = np.empty((steps + 1, *grid.shape), dtype=np.int8)
    history[0] = grid
    for generation in range(steps):
        history[generation + 1] = step(history[generation], rule, generation)
    return history


def hamming_divergence(
    grid: np.ndarray,
    steps: int,
    rule: Rule = Rule(),
    coordinate: tuple[int, int] | None = None,
) -> np.ndarray:
    """Compare two trajectories separated by one local trit perturbation."""
    perturbed = grid.copy()
    coordinate = coordinate or (grid.shape[0] // 2, grid.shape[1] // 2)
    i, j = coordinate
    perturbed[i, j] = {-1: 0, 0: 1, 1: -1}[int(perturbed[i, j])]
    a = rollout(grid, steps, rule)
    b = rollout(perturbed, steps, rule)
    return np.mean(a != b, axis=(1, 2))


class CountMoE:
    """Three tabular experts keyed by centre state and neighbour counts."""

    def __init__(self) -> None:
        # centre index {-1,0,+1}->{0,1,2}; counts each range 0..8; class index idem.
        self.counts = np.ones((3, 9, 9, 3), dtype=np.int64)

    @staticmethod
    def _state_index(values: np.ndarray) -> np.ndarray:
        return values.astype(np.int64) + 1

    def fit_pair(self, grid: np.ndarray, target: np.ndarray) -> None:
        pos, neg = neighbour_counts(grid)
        centre = self._state_index(grid)
        label = self._state_index(target)
        np.add.at(self.counts, (centre.ravel(), pos.ravel(), neg.ravel(), label.ravel()), 1)

    def fit_rollouts(self, histories: Iterable[np.ndarray]) -> "CountMoE":
        for history in histories:
            for grid, target in zip(history[:-1], history[1:]):
                self.fit_pair(grid, target)
        return self

    def predict(self, grid: np.ndarray) -> np.ndarray:
        pos, neg = neighbour_counts(grid)
        centre = self._state_index(grid)
        classes = self.counts[centre, pos, neg].argmax(axis=-1)
        return (classes - 1).astype(np.int8)

    def accuracy(self, history: np.ndarray) -> float:
        correct = total = 0
        for grid, target in zip(history[:-1], history[1:]):
            prediction = self.predict(grid)
            correct += int((prediction == target).sum())
            total += target.size
        return correct / total if total else float("nan")


def motif_census(history: np.ndarray, max_period: int = 8) -> dict[str, int]:
    """Count whole-grid recurrences as fixed points or short oscillators.

    This is deliberately conservative: it does not claim to identify translated
    gliders.  It supplies a sound first census before adding connected-component
    tracking and translation equivalence.
    """
    result = {"fixed_points": 0, "oscillators": 0, "minimum_period": 0}
    final = history[-1]
    for period in range(1, min(max_period, len(history) - 1) + 1):
        if np.array_equal(final, history[-1 - period]):
            result["minimum_period"] = period
            if period == 1:
                result["fixed_points"] = 1
            else:
                result["oscillators"] = 1
            break
    return result


def random_grid(size: int, density: float, rng: np.random.Generator) -> np.ndarray:
    active = rng.random((size, size)) < density
    signs = rng.choice(np.array([-1, 1], dtype=np.int8), size=(size, size))
    return np.where(active, signs, 0).astype(np.int8)


def experiment(args: argparse.Namespace) -> dict[str, object]:
    rng = np.random.default_rng(args.seed)
    rule = Rule(
        birth=tuple(args.birth),
        survive=tuple(args.survive),
        tie_mode=args.tie_mode,
        field_alpha=args.field_alpha,
    )

    train_histories = [
        rollout(random_grid(args.size, args.density, rng), args.steps, rule)
        for _ in range(args.train_rollouts)
    ]
    test = rollout(random_grid(args.size, args.density, rng), args.steps, rule)
    learner = CountMoE().fit_rollouts(train_histories)
    divergence = hamming_divergence(test[0], args.steps, rule)

    fractions = {
        "negative": float(np.mean(test[-1] == -1)),
        "hold": float(np.mean(test[-1] == 0)),
        "positive": float(np.mean(test[-1] == 1)),
    }
    return {
        "rule": {
            "birth": list(rule.birth),
            "survive": list(rule.survive),
            "tie_mode": rule.tie_mode,
            "field_alpha": rule.field_alpha,
        },
        "one_step_moe_accuracy": learner.accuracy(test),
        "final_state_fractions": fractions,
        "final_hamming_divergence": float(divergence[-1]),
        "peak_hamming_divergence": float(divergence.max()),
        "motif_census": motif_census(test),
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--size", type=int, default=96)
    parser.add_argument("--steps", type=int, default=128)
    parser.add_argument("--train-rollouts", type=int, default=8)
    parser.add_argument("--density", type=float, default=0.36)
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--birth", type=int, nargs="+", default=[3, 4])
    parser.add_argument("--survive", type=int, nargs="+", default=[2, 3, 4])
    parser.add_argument(
        "--tie-mode",
        choices=["hold", "positive", "negative", "checker", "hash"],
        default="hash",
    )
    parser.add_argument("--field-alpha", type=float, default=0.0)
    return parser.parse_args()


def main() -> None:
    report = experiment(parse_args())
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
