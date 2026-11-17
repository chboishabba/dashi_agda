import unittest

from scripts.exceptional_f4_derivation_maxcut_probe import verify


class ExceptionalF4DerivationMaxCutProbeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.out = verify()

    def test_derivation_space_is_52_dimensional(self):
        self.assertEqual(self.out["constraint_rank"], 677)
        self.assertEqual(self.out["derivation_dimension"], 52)
        self.assertEqual(self.out["inner_derivation_span"], 52)

    def test_derivation_lie_algebra_is_perfect_and_centreless(self):
        self.assertEqual(self.out["derived_lie_span"], 52)
        self.assertEqual(self.out["derivation_centre_dimension"], 0)

    def test_only_one_common_fixed_vector(self):
        self.assertEqual(self.out["common_fixed_dimension"], 1)

    def test_rational_form_obstruction(self):
        self.assertEqual(self.out["first_tits_trace_signature"], (15, 12))
        self.assertEqual(self.out["compact_albert_trace_signature"], (27, 0))
        self.assertEqual(int(self.out["negative_trace_square_witness"]), -2)

    def test_corrected_basis_support_census(self):
        self.assertEqual(self.out["basis_pair_support"], {0: 414, 1: 291, 2: 24})


if __name__ == "__main__":
    unittest.main()
