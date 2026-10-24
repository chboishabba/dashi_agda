#!/usr/bin/env python3
"""Regression for conditional source-typed D4 signed C3-local-system model."""
from pathlib import Path
import importlib.util
import unittest

ROOT=Path(__file__).resolve().parents[1]
SPEC=importlib.util.spec_from_file_location(
    "signed_c3", ROOT/"scripts/jfine_3b_signed_c3_orbit_repair.py")
m=importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(m)

class SignedC3ModelTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):cls.receipt=m.audit()

    def test_original_basis_size_and_orbit_selection(self):
        a=self.receipt
        self.assertEqual(a["selected_orbits"],{"fixed":1,"axis":9,"diagonal":9})
        self.assertEqual(a["signed_quotient_basis_labels"],73)
        self.assertEqual(a["signed_full_c3_basis_labels"],219)
        self.assertEqual(a["D4_and_C3_checks"],14016)
    def test_character_repair_and_real_residual(self):
        a=self.receipt
        self.assertEqual(a["trace_corrections"],{
            "one":0,"half":0,"quarter":0,"axis":-38,"diagonal":-38})
        self.assertEqual(a["residual_character"],{
            "one":53,"half":-3,"quarter":-3,"axis":-11,"diagonal":-11})
        self.assertEqual(a["residual_irreducible_multiplicities"],{
            "A1":0,"A2":11,"B1":7,"B2":7,"E":14})
    def test_nonpromotion_and_h4_failure(self):
        a=self.receipt
        self.assertTrue(a["centre_C3_conjugacy_verified"])
        self.assertFalse(a["preserves_source_regular_H4_action"])
        self.assertTrue(a["regular_H4_incompatibility_witness"])
        self.assertFalse(a["actual_Monster_normalizer_constructed"])

if __name__=="__main__":unittest.main()
