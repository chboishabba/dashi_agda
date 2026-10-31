#!/usr/bin/env python3
"""stdlib-only local tests for the existing dashi-repo symbol-search adapter.

Not an Agda/Lean compiler test; does not query network, CI or any SQLite DB.
"""
from pathlib import Path
import importlib.util
import json
import shutil
import subprocess
import sys
import tempfile
import unittest


HERE = Path(__file__).resolve().parent
RUNNER = HERE / "run_openai_math_symbol_snowball.py"
TERMS = (HERE.parent / "docs/superpowers/plans"
         / "2026-10-31-local-symbol-snowball-terms.json")
spec = importlib.util.spec_from_file_location("dashi_symbol_snowball", RUNNER)
search = importlib.util.module_from_spec(spec)
spec.loader.exec_module(search)


class LocalSymbolSnowballTest(unittest.TestCase):
    def test_pack_is_reuse_first_and_all_lanes_explicit(self):
        payload = json.loads(TERMS.read_text())
        self.assertEqual(payload["schema"], "dashi-symbol-snowball-v1")
        groups = payload["groups"]
        self.assertEqual(len(groups), 13)
        self.assertGreaterEqual(sum(len(g["search_terms"]) for g in groups), 150)
        self.assertEqual(groups[0]["lane"], "P0")
        self.assertIn("P4", [g["lane"] for g in groups])
        self.assertIn("R06", [g["lane"] for g in groups])
        all_terms = [t for g in groups for t in g["search_terms"]]
        self.assertIn("uniqueUsedCoordinates", all_terms)
        self.assertIn("formulaBitLength_upper", all_terms)
        self.assertIn("laterJump", all_terms)

    def test_dedup_and_priority(self):
        jobs = list(search.parse_groups(TERMS, set(), 10))
        self.assertEqual(len(jobs), 10)
        self.assertEqual(len({term for _, term in jobs}), 10)
        self.assertEqual(jobs[0][0]["lane"], "P0")
        with self.assertRaisesRegex(ValueError, "unknown group"):
            list(search.parse_groups(TERMS, {"NONEXISTENT"}, 3))

    def test_dry_run_does_not_need_native_database(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp) / "agda"
            lean = Path(temp) / "lean"
            root.mkdir()
            lean.mkdir()
            (root / "Owner.agda").write_text("uniqueUsedCoordinates : Set\n")
            completed = subprocess.run(
                [sys.executable, str(RUNNER), "--agda-root", str(root),
                 "--lean-root", str(lean), "--mode", "plan",
                 "--group", "P1", "--related", "--max-terms", "2"],
                text=True, capture_output=True, check=True)
            self.assertIn("dashi-repo symbol", completed.stdout)
            self.assertIn("rg --no-heading", completed.stdout)
            self.assertIn("uniqueUsedCoordinates", completed.stdout)
            self.assertFalse((root / ".dashi").exists())

    @unittest.skipUnless(shutil.which("rg"), "ripgrep not installed")
    def test_grep_matches_agda_and_lean_without_false_proof_claim(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp) / "agda"
            lean = Path(temp) / "lean"
            root.mkdir()
            lean.mkdir()
            (root / "Golden.agda").write_text(
                "uniqueUsedCoordinates : Set\nuniqueUsedCoordinates = Set\n")
            (lean / "Adapter.lean").write_text(
                "theorem uniqueUsedCoordinates : True := trivial\n")
            result = subprocess.run(
                [sys.executable, str(RUNNER), "--agda-root", str(root),
                 "--lean-root", str(lean), "--group", "P1",
                 "--mode", "grep", "--max-terms", "2"],
                text=True, capture_output=True, check=True)
            self.assertIn("Golden.agda", result.stdout)
            self.assertIn("Adapter.lean", result.stdout)
            self.assertIn("never a theorem-acceptance", result.stdout)

    def test_requires_positive_limits_and_valid_root(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            result = subprocess.run(
                [sys.executable, str(RUNNER), "--agda-root", str(root),
                 "--mode", "plan", "--max-lines", "0"],
                text=True, capture_output=True)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("--max-lines must be positive", result.stderr)


if __name__ == "__main__":
    unittest.main()
