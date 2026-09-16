#!/usr/bin/env python3
from __future__ import annotations

import importlib.util
from pathlib import Path
import unittest

HERE = Path(__file__).resolve().parent
MODULE_PATH = HERE.parent / "slr_world_round_accounting.py"
spec = importlib.util.spec_from_file_location("slr_world_round_accounting", MODULE_PATH)
assert spec and spec.loader
accounting = importlib.util.module_from_spec(spec)
spec.loader.exec_module(accounting)


class WorldRoundAccountingTests(unittest.TestCase):
    def test_round_growth_separates_structural_and_article_pnf_atoms(self) -> None:
        receipt = accounting.world_growth_receipt(
            prior_canonical_atoms=4031,
            structural_canonical_atoms=4935,
            final_canonical_atoms=9334,
        )
        self.assertEqual(receipt["structural_atoms_added"], 904)
        self.assertEqual(receipt["article_pnf_atoms_added"], 4399)
        self.assertEqual(receipt["total_atoms_added"], 5303)
        self.assertEqual(receipt["structural_atoms_added"] + receipt["article_pnf_atoms_added"], receipt["total_atoms_added"])
        self.assertFalse(receipt["atom_growth_creates_claim_truth"])

    def test_accounting_rejects_non_monotone_stage_counts(self) -> None:
        with self.assertRaises(ValueError):
            accounting.world_growth_receipt(
                prior_canonical_atoms=100,
                structural_canonical_atoms=90,
                final_canonical_atoms=110,
            )


if __name__ == "__main__":
    unittest.main()
