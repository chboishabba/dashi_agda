#!/usr/bin/env python3
"""Regression contract for the multiplicative Dirichlet-phase max-cut."""

from pathlib import Path
import unittest

import monster_climbing_gym_dirichlet_phase as phase

ROOT = Path(__file__).resolve().parent.parent
DISCOVERY = ROOT / "scripts" / "data" / "monster_climbing_gym_first_849_zeros.json"
HELD_OUT = ROOT / "scripts" / "data" / "monster_climbing_gym_zeros_850_1698.json"


class MonsterClimbingGymDirichletPhaseTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.discovery = phase.load_zero_cache(DISCOVERY)
        cls.held_out = phase.load_zero_cache(HELD_OUT)
        cls.discovery_result = phase.analyse_window(
            cls.discovery,
            window_label="zeros-1-849",
            lower_height=0.0,
        )
        cls.held_out_result = phase.analyse_window(
            cls.held_out,
            window_label="zeros-850-1698",
            lower_height=cls.discovery[-1],
        )

    def test_discovery_raw_reproduces_existing_phase_control(self) -> None:
        raw = self.discovery_result["raw"]
        self.assertAlmostEqual(raw["actual_mean_energy"], 59.76582455, places=6)
        self.assertEqual(raw["energy_lower_or_equal_count"], 3459)
        self.assertAlmostEqual(raw["actual_mean_vector_magnitude"], 0.31545946, places=6)
        self.assertEqual(raw["coherence_upper_or_equal_count"], 541)

    def test_landau_residual_is_explicitly_diagnostic(self) -> None:
        residual = self.discovery_result["landau_prime_main_residual"]
        self.assertAlmostEqual(residual["actual_mean_vector_magnitude"], 0.04141800, places=6)
        self.assertEqual(residual["coherence_upper_or_equal_count"], 248)
        self.assertFalse(self.discovery_result["landau_main_term_claimed_exact_finite_formula"])
        self.assertFalse(self.discovery_result["confirmatory_p_value_claimed"])

    def test_held_out_window_is_disjoint_and_less_extreme_raw(self) -> None:
        self.assertEqual(self.held_out_result["zero_count"], 849)
        raw = self.held_out_result["raw"]
        self.assertAlmostEqual(raw["actual_mean_vector_magnitude"], 0.20313558, places=6)
        self.assertEqual(raw["coherence_upper_or_equal_count"], 1067)
        self.assertGreater(raw["coherence_upper_tail_fraction"], 0.06)

    def test_held_out_landau_residual_does_not_replicate_discovery_tail(self) -> None:
        residual = self.held_out_result["landau_prime_main_residual"]
        self.assertAlmostEqual(residual["actual_mean_vector_magnitude"], 0.01525212, places=6)
        self.assertEqual(residual["coherence_upper_or_equal_count"], 7367)
        self.assertGreater(residual["coherence_upper_tail_fraction"], 0.47)
        self.assertLess(residual["coherence_upper_tail_fraction"], 0.48)
        self.assertFalse(self.held_out_result["replicated_monster_specific_anomaly_claimed"])

    def test_moments_expose_twenty_channels_and_hermitian_kernel(self) -> None:
        moments = self.discovery_result["prime_moments"]
        kernel = self.discovery_result["pair_kernel"]
        self.assertEqual(len(moments), 20)
        self.assertEqual(len(kernel), 20)
        self.assertTrue(all(len(row) == 20 for row in kernel))
        for i in range(20):
            self.assertAlmostEqual(kernel[i][i]["re"], 1.0, places=12)
            self.assertAlmostEqual(kernel[i][i]["im"], 0.0, places=12)
            for j in range(20):
                self.assertAlmostEqual(kernel[i][j]["re"], kernel[j][i]["re"], places=12)
                self.assertAlmostEqual(kernel[i][j]["im"], -kernel[j][i]["im"], places=12)


if __name__ == "__main__":
    unittest.main()
