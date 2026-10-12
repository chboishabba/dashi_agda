#!/usr/bin/env python3
"""Regression contract for the JMD Monster Climbing Gym replay.

TDD owner: committed before the producer implementation.  The full fixture is
small enough to run deterministically from the checked-in 849-zero cache.
"""

from pathlib import Path
import json
import unittest

import monster_climbing_gym_replay as replay


ROOT = Path(__file__).resolve().parent.parent
ZERO_CACHE = ROOT / "scripts" / "data" / "monster_climbing_gym_first_849_zeros.json"

EXPECTED = {
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


class MonsterClimbingGymReplayTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        payload = json.loads(ZERO_CACHE.read_text())
        cls.zeros = [float(x) for x in payload["ordinates"]]

    def test_cache_contains_exactly_849_ordered_positive_ordinates(self) -> None:
        self.assertEqual(len(self.zeros), 849)
        self.assertTrue(all(x > 0 for x in self.zeros))
        self.assertTrue(all(a < b for a, b in zip(self.zeros, self.zeros[1:])))

    def test_one_unit_guard_replays_all_reported_hole_and_mutual_counts(self) -> None:
        observed = replay.replay_table(self.zeros, guard=1.0)
        compact = {
            (row["prime"], row["exponent"]): (row["holes"], row["mutual_pairs"])
            for row in observed
        }
        self.assertEqual(compact, EXPECTED)

    def test_p71_saturates_all_849_zeros(self) -> None:
        row = replay.replay_wall(self.zeros, prime=71, exponent=1, guard=1.0)
        self.assertEqual(row["mutual_pairs"], 849)

    def test_shifted_lattice_control_keeps_p71_saturated(self) -> None:
        for shift in (-1.0, -0.7, 0.0, 0.4, 1.0):
            row = replay.replay_wall(
                self.zeros, prime=71, exponent=1, guard=1.0, lattice_shift=shift
            )
            self.assertEqual(row["mutual_pairs"], 849)


if __name__ == "__main__":
    unittest.main()
