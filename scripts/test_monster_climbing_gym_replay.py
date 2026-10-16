#!/usr/bin/env python3
"""Regression contract for the JMD Monster Climbing Gym replay."""

from pathlib import Path
import json
import unittest

import monster_climbing_gym_replay as replay

ROOT = Path(__file__).resolve().parent.parent
ZERO_CACHE = ROOT / "scripts" / "data" / "monster_climbing_gym_first_849_zeros.json"

EXPECTED = {
    (2, 1): (271, 270), (3, 1): (644, 581), (5, 1): (1571, 820),
    (7, 1): (2660, 845), (11, 1): (5151, 849), (2, 2): (542, 513),
    (3, 2): (1931, 841), (2, 3): (1083, 773), (13, 1): (6511, 849),
    (71, 1): (59099, 849),
}

CONTROL_EXPECTED = {
    37: (26090, 849), 43: (31582, 849), 53: (41091, 849),
    61: (48967, 849), 67: (55012, 849),
}

SOURCE_SHIFT_SUMMARIES = {
    (2, 1): (270.3, 0.9), (3, 1): (594.0, 8.4), (5, 1): (825.4, 3.2),
    (7, 1): (845.7, 0.9), (11, 1): (848.5, 0.6), (2, 2): (519.3, 4.3),
    (3, 2): (837.4, 2.5), (2, 3): (771.3, 3.9), (13, 1): (848.7, 0.5),
    (71, 1): (849.0, 0.0),
}


class MonsterClimbingGymReplayTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.zeros = replay.load_zero_cache(ZERO_CACHE)

    def test_cache_metadata_contract_is_fail_closed(self) -> None:
        payload = json.loads(ZERO_CACHE.read_text())
        self.assertEqual(payload["schema_version"], replay.CACHE_SCHEMA_VERSION)
        self.assertEqual(payload["generator"], replay.CACHE_GENERATOR)
        self.assertEqual(payload["scale"], 10000)
        self.assertEqual(payload["count"], 849)
        self.assertEqual(len(payload["first_plus_deltas"]), payload["count"])

    def test_cache_contains_exactly_849_ordered_positive_ordinates(self) -> None:
        self.assertEqual(len(self.zeros), 849)
        self.assertTrue(all(x > 0 for x in self.zeros))
        self.assertTrue(all(a < b for a, b in zip(self.zeros, self.zeros[1:])))

    def test_one_unit_guard_replays_all_reported_hole_and_mutual_counts(self) -> None:
        observed = replay.replay_table(self.zeros, guard=1.0)
        compact = {(r["prime"], r["exponent"]): (r["holes"], r["mutual_pairs"]) for r in observed}
        self.assertEqual(compact, EXPECTED)

    def test_all_five_non_ogg_controls_also_saturate(self) -> None:
        observed = replay.replay_non_ogg_controls(self.zeros, guard=1.0)
        compact = {r["prime"]: (r["holes"], r["mutual_pairs"]) for r in observed}
        self.assertEqual(compact, CONTROL_EXPECTED)

    def test_p71_saturates_all_849_zeros(self) -> None:
        row = replay.replay_wall(self.zeros, prime=71, exponent=1, guard=1.0)
        self.assertEqual(row["mutual_pairs"], 849)

    def test_shifted_lattice_control_keeps_p71_saturated(self) -> None:
        for shift in (-1.0, -0.7, 0.0, 0.4, 1.0):
            row = replay.replay_wall(self.zeros, prime=71, exponent=1, guard=1.0, lattice_shift=shift)
            self.assertEqual(row["mutual_pairs"], 849)

    def test_deterministic_phase_grid_is_consistent_with_reported_shift_null(self) -> None:
        # The source gives only rounded mean/SD summaries, not the sampled shifts
        # or RNG seed.  A deterministic full-period phase grid should reproduce
        # the same null family within finite-sample/rounding tolerance, but must
        # not be claimed as the exact source random sample.
        for wall, (source_mean, source_sd) in SOURCE_SHIFT_SUMMARIES.items():
            summary = replay.phase_grid_control_summary(
                self.zeros, prime=wall[0], exponent=wall[1], steps=720, guard=1.0
            )
            self.assertLessEqual(abs(summary["mean"] - source_mean), 1.1)
            self.assertLessEqual(abs(summary["population_sd"] - source_sd), 0.8)
        p71 = replay.phase_grid_control_summary(
            self.zeros, prime=71, exponent=1, steps=720, guard=1.0
        )
        self.assertEqual(p71["minimum"], 849)
        self.assertEqual(p71["maximum"], 849)


if __name__ == "__main__":
    unittest.main()
