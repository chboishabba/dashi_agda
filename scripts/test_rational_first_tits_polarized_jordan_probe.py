#!/usr/bin/env python3
from __future__ import annotations

import unittest

import rational_first_tits_polarized_jordan_probe as probe


class RationalFirstTitsPolarizedJordanTests(unittest.TestCase):
    def test_structure_constant_support_matches_existing_receipt(self):
        result = probe.verify()
        self.assertEqual(result["basis_product_support"], {0: 414, 1: 291, 2: 24})

    def test_all_basis_quadruples_pass(self):
        result = probe.verify()
        self.assertEqual(result["basis_quadruples_checked"], 27**4)
        self.assertTrue(result["all_polarized_jordan_quadruples_zero"])
        self.assertIsNone(result["first_failure"])


if __name__ == "__main__":
    unittest.main()
