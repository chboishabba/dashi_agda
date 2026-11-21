import unittest
from dataclasses import replace
from scripts.treasury_opposing_flows_20261121 import (
    OpposingFlows, YieldSign, rival_fixture_pair, sensitivity_to_haven
)

class OpposingFlowsTests(unittest.TestCase):
    def test_opposite_outcomes_same_jpy(self):
        flight, sales = rival_fixture_pair()
        self.assertEqual((flight.japan_repatriation, flight.treasury_forced_sales),
                         (sales.japan_repatriation, sales.treasury_forced_sales))
        self.assertEqual((flight.downward, flight.upward), (10, 6))
        self.assertEqual((sales.downward, sales.upward), (2, 6))
        self.assertEqual((flight.signed_result(), sales.signed_result()),
                         (YieldSign.DOWN, YieldSign.UP))

    def test_no_unverified_common_basis_promoted(self):
        flight, _ = rival_fixture_pair()
        self.assertIsNone(replace(flight, common_basis_receipt=False).signed_result())

    def test_balanced_and_haven_sensitivity(self):
        _, sales = rival_fixture_pair()
        self.assertEqual(sensitivity_to_haven(sales, (1, 5, 8)),
                         (YieldSign.UP, YieldSign.FLAT, YieldSign.DOWN))

    def test_invalid_negative_and_nonfinite(self):
        for v in (-1, float("nan"), float("inf")):
            with self.subTest(v=v):
                with self.assertRaises(ValueError):
                    OpposingFlows(v, 0, 0, 0, 0, True)

    def test_same_yield_sign_does_not_choose_objective(self):
        # A sign is an observation, not a classification into policy H0-H4.
        f, _ = rival_fixture_pair()
        for hypothesis in ("H0", "H1", "H2", "H3", "H4"):
            with self.subTest(hypothesis=hypothesis):
                self.assertEqual(f.signed_result(), YieldSign.DOWN)

if __name__ == "__main__":
    unittest.main()
