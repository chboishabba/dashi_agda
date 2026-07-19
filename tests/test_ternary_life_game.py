from pathlib import Path
import sys

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))

from ternary_life_game import CountMoE, Rule, motif_census, neighbour_counts, rollout, step


def test_neighbour_counts_wrap_on_torus() -> None:
    grid = np.zeros((5, 5), dtype=np.int8)
    grid[0, 0] = 1
    positive, negative = neighbour_counts(grid)
    assert positive[4, 4] == 1
    assert negative.sum() == 0


def test_classic_positive_birth() -> None:
    grid = np.zeros((7, 7), dtype=np.int8)
    grid[2, 3] = 1
    grid[3, 2] = 1
    grid[3, 4] = -1
    next_grid = step(grid, Rule(birth=(3,), survive=(2, 3), tie_mode="hold"))
    assert next_grid[3, 3] == 1


def test_even_tie_can_hold() -> None:
    grid = np.zeros((7, 7), dtype=np.int8)
    grid[2, 3] = 1
    grid[3, 2] = 1
    grid[3, 4] = -1
    grid[4, 3] = -1
    next_grid = step(grid, Rule(tie_mode="hold"))
    assert next_grid[3, 3] == 0


def test_count_moe_learns_deterministic_hold_rule() -> None:
    rng = np.random.default_rng(7)
    rule = Rule(tie_mode="hold")
    histories = []
    for _ in range(24):
        grid = rng.choice(
            np.array([-1, 0, 1], dtype=np.int8),
            size=(24, 24),
            p=(0.18, 0.64, 0.18),
        )
        histories.append(rollout(grid, 12, rule))

    learner = CountMoE().fit_rollouts(histories[:-1])
    assert learner.accuracy(histories[-1]) > 0.97


def test_fixed_point_census() -> None:
    history = np.zeros((3, 8, 8), dtype=np.int8)
    assert motif_census(history) == {
        "fixed_points": 1,
        "oscillators": 0,
        "minimum_period": 1,
    }
