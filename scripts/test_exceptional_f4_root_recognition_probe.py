import unittest

from scripts.exceptional_f4_root_recognition_probe import verify


class F4RootRecognitionProbeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.out = verify()

    def test_rank_four_torus_and_weight_27(self):
        self.assertEqual(self.out["primitive_toral_derivations"], 12)
        self.assertEqual(self.out["carrier_zero_weight_dimension"], 3)
        self.assertEqual(self.out["carrier_nonzero_weight_count"], 24)

    def test_adjoint_root_decomposition(self):
        self.assertEqual(self.out["adjoint_zero_weight_dimension"], 4)
        self.assertEqual(self.out["adjoint_root_count"], 48)
        self.assertTrue(self.out["root_spaces_one_dimensional"])

    def test_explicit_f4_root_transport(self):
        self.assertTrue(self.out["transported_root_set_equals_standard_f4_mod3"])
        self.assertEqual(
            self.out["gl4_change"],
            [[1, 2, 1, 1], [1, 1, 2, 1], [2, 2, 2, 2], [0, 0, 0, 1]],
        )


if __name__ == "__main__":
    unittest.main()
