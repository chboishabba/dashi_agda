import unittest

from scripts.exceptional_gravity_atomic_clock_calibration_probe import verify


class ExceptionalGravityAtomicClockCalibrationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.out = verify()

    def test_candidate_atomic_edge(self):
        self.assertAlmostEqual(self.out["candidate_edge_mm"], 32.61225571749406, places=12)

    def test_unit_amplitude_is_empirically_too_large(self):
        self.assertAlmostEqual(
            self.out["unit_amplitude_vertical_gradient_per_mm"],
            0.02139301324778956,
            places=15,
        )
        self.assertGreater(self.out["unit_over_theory_ratio"], 1e17)

    def test_required_weak_amplitude(self):
        self.assertAlmostEqual(
            self.out["epsilon_to_match_theory"],
            6.39852457177233e-18,
            places=30,
        )
        self.assertAlmostEqual(
            self.out["epsilon_to_match_corrected_central"],
            5.752801908565952e-18,
            places=30,
        )


if __name__ == "__main__":
    unittest.main()
