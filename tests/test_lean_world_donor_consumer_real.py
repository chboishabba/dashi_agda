#!/usr/bin/env python3
"""Optional exact-toolchain Lean donor -> consumer acceptance test."""
from __future__ import annotations
import os
from pathlib import Path
import shutil
import sys
import unittest

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/"scripts"))
from run_lean_world_donor_consumer_smoke import run


class DonorConsumerRealLean(unittest.TestCase):
    def test_actual_pinned_lean_two_module_reuse(self):
        configured=os.environ.get("DASHI_LEAN_BIN")
        if not configured:
            self.skipTest("DASHI_LEAN_BIN not set: no pinned compiler receipt")
        lean=Path(configured)
        self.assertTrue(lean.is_absolute(),"must provide exact pinned Lean path")
        self.assertTrue(lean.is_file(),"pinned Lean binary unavailable")
        result=run(lean)
        self.assertTrue(result["second_lean_elaboration_succeeded"])
        self.assertFalse(result["retrieved_from_canonical_world"])
        self.assertFalse(result["independent_checker_certified"])
        self.assertEqual(len(result["consumer_olean_sha256"]),64)


if __name__=="__main__":
    unittest.main()
