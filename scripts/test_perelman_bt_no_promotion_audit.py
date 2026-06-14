#!/usr/bin/env python3
"""Tests for scripts/perelman_bt_no_promotion_audit.py."""

from __future__ import annotations

import importlib.util
import subprocess
import sys
import unittest
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
AUDIT_PATH = REPO_ROOT / "scripts" / "perelman_bt_no_promotion_audit.py"


def load_audit_module():
    spec = importlib.util.spec_from_file_location("perelman_bt_no_promotion_audit", AUDIT_PATH)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"unable to import audit script at {AUDIT_PATH}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


class PerelmanBTNoPromotionAuditTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.audit = load_audit_module()

    def test_current_audit_exits_zero(self) -> None:
        result = subprocess.run(
            [sys.executable, str(AUDIT_PATH)],
            cwd=REPO_ROOT,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
        )
        self.assertEqual(
            result.returncode,
            0,
            msg=f"stdout:\n{result.stdout}\nstderr:\n{result.stderr}",
        )
        self.assertIn("perelman_bt_no_promotion_audit: PASS", result.stdout)

    def test_forbidden_token_detection_on_artificial_texts(self) -> None:
        forbidden = self.audit.FORBIDDEN_TOKENS[0]
        texts = {
            "clean.agda": "module Clean where\nsafe : Bool\nsafe = true\n",
            "bad.agda": f"module Bad where\nbadToken = {forbidden}\n",
        }

        hits = self.audit.find_forbidden(texts)

        self.assertEqual(len(hits), 1)
        self.assertEqual(hits[0].relpath, "bad.agda")
        self.assertEqual(hits[0].line, 2)
        self.assertEqual(hits[0].token, forbidden)

    def test_missing_required_pattern_detection_on_artificial_texts(self) -> None:
        omitted = self.audit.REQUIRED_TOKENS[-1]
        present_tokens = self.audit.REQUIRED_TOKENS[:-1]
        texts = {"synthetic.agda": "\n".join(present_tokens)}

        missing = self.audit.find_missing_required(texts)

        self.assertEqual(missing, [omitted])


if __name__ == "__main__":
    unittest.main()
