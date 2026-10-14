#!/usr/bin/env python3
"""Regression contract for the phase-sensitive Ogg-vs-control max-cut."""

from pathlib import Path
import json
import unittest

import monster_climbing_gym_phase_control as phase

ROOT = Path(__file__).resolve().parent.parent
ZERO_CACHE = ROOT / "scripts" / "data" / "monster_climbing_gym_first_849_zeros.json"


def decode_cache(path: Path) -> list[float]:
    payload = json.loads(path.read_text())
    scale = int(payload["scale"])
    encoded = [int(x) for x in payload["first_plus_deltas"]]
    values, current = [], 0
    for index, value in enumerate(encoded):
        current = value if index == 0 else current + value
        values.append(current / scale)
    return values


class MonsterClimbingGymPhaseControlTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.zeros = decode_cache(ZERO_CACHE)
        cls.result = phase.exhaustive_balanced_partition_control(cls.zeros)

    def test_balanced_partition_space_is_exhaustive(self) -> None:
        self.assertEqual(self.result["assignment_count"], 15504)
        self.assertEqual(self.result["ogg_count"], 15)
        self.assertEqual(self.result["control_count"], 5)

    def test_actual_partition_energy_is_not_tail_extreme(self) -> None:
        self.assertAlmostEqual(self.result["actual_mean_energy"], 59.7658245, places=5)
        self.assertEqual(self.result["energy_lower_or_equal_count"], 3459)
        self.assertGreater(self.result["energy_lower_tail_fraction"], 0.20)
        self.assertLess(self.result["energy_lower_tail_fraction"], 0.25)

    def test_mean_vector_coherence_is_exploratory_upper_tail(self) -> None:
        self.assertAlmostEqual(self.result["actual_mean_vector_magnitude"], 0.31545946, places=6)
        self.assertEqual(self.result["coherence_upper_or_equal_count"], 541)
        self.assertGreater(self.result["coherence_upper_tail_fraction"], 0.03)
        self.assertLess(self.result["coherence_upper_tail_fraction"], 0.04)

    def test_claim_boundary_refuses_post_hoc_promotion(self) -> None:
        self.assertFalse(self.result["confirmatory_p_value_claimed"])
        self.assertFalse(self.result["monster_specificity_claimed"])
        self.assertTrue(self.result["multiple_statistic_warning"])


if __name__ == "__main__":
    unittest.main()
