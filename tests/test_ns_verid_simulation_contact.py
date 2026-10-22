"""Tests for the VERID/NS paired-simulation contract."""
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
from ns_verid_simulation_contact import SEEDS, benchmark


class NumericalContactTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.result = benchmark(steps=2, dt=0.001)

    def test_reproducible_digest(self):
        self.assertEqual(self.result, benchmark(steps=2, dt=0.001))

    def test_matching_horizons_and_distinct_time_steps(self):
        self.assertEqual(len(self.result["comparisons"]), len(SEEDS))
        self.assertEqual(self.result["design"]["comparison_horizon"], 0.002)
        for row in self.result["comparisons"]:
            self.assertEqual(row["model_steps"], 2)
            self.assertEqual(row["simulation_steps"], 4)
            self.assertEqual(set(row["observable_errors"]), {
                "final_energy", "integrated_weighted_five_halves",
                "integrated_vorticity_fourier_l1"
            })

    def test_authority_firewalls(self):
        a = self.result["authority"]
        for field in ("independent_solver_validation", "physical_lab_validation",
                      "continuum_error_bound", "clay_navier_stokes",
                      "automatic_promotion"):
            self.assertFalse(a[field])

    def test_projection_collision_is_not_global_sufficiency(self):
        p = self.result["projection"]
        self.assertTrue(p["coarse_collision"])
        self.assertTrue(p["seed_coordinate_separates"])
        self.assertFalse(p["consumer_sufficiency_claim"])

    def test_invalid_steps_rejected(self):
        with self.assertRaises(ValueError):
            benchmark(steps=0)
        with self.assertRaises(ValueError):
            benchmark(dt=-0.001)


if __name__ == "__main__":
    unittest.main()
