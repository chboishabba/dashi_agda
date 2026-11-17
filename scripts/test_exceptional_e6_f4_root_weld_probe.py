import unittest

from scripts.exceptional_e6_f4_root_weld_probe import verify


class ExceptionalE6F4RootWeldProbeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.out = verify()

    def test_norm_symmetry_is_e6_sized_on_same_cubic(self):
        self.assertEqual(self.out["cubic_monomial_count"], 45)
        self.assertEqual(self.out["norm_symmetry_rank"], 651)
        self.assertEqual(self.out["norm_symmetry_dimension"], 78)
        self.assertEqual(self.out["e6_cartan_dimension"], 6)
        self.assertEqual(self.out["e6_root_count"], 72)

    def test_unit_stabilizer_equals_derivations_locally(self):
        self.assertEqual(self.out["unit_stabilizer_rank"], 677)
        self.assertEqual(self.out["unit_stabilizer_dimension"], 52)
        self.assertEqual(self.out["derivation_rank"], 677)
        self.assertEqual(self.out["derivation_dimension"], 52)
        self.assertTrue(self.out["unit_stabilizer_equals_derivations_mod101"])

    def test_same_27_weight_lines_reproduce_schlafli_geometry(self):
        self.assertEqual(self.out["minuscule_srg"], (27, 16, 10, 8))

    def test_derivation_roots_weld_to_repo_f4_root_datum(self):
        self.assertEqual(self.out["f4_cartan_dimension"], 4)
        self.assertEqual(self.out["f4_root_count"], 48)
        self.assertEqual(self.out["f4_short_long_counts"], (24, 24))
        self.assertTrue(self.out["f4_repo_root_set_weld"])
        self.assertEqual(self.out["f4_metric_scale"], 72)


if __name__ == "__main__":
    unittest.main()
