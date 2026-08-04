#!/usr/bin/env python3
"""Unit tests for the fail-closed Luo submission audit scanner."""

from __future__ import annotations

import importlib.util
import tempfile
import unittest
from pathlib import Path

SCRIPT = Path(__file__).with_name("generate_ns_luo_submission_audit.py")
SPEC = importlib.util.spec_from_file_location("ns_luo_submission_audit", SCRIPT)
if SPEC is None or SPEC.loader is None:
    raise RuntimeError(f"could not load {SCRIPT}")
AUDIT = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(AUDIT)


class CommentStrippingTests(unittest.TestCase):
    def test_nested_block_comments_are_removed_and_newlines_preserved(self) -> None:
        source = "x\n{- outer ?\n  {- inner postulate -}\n-}\ny\n"
        stripped = AUDIT.strip_agda_comments(source)
        self.assertEqual(stripped.count("\n"), source.count("\n"))
        self.assertNotIn("?", stripped)
        self.assertNotIn("postulate", stripped)
        self.assertIn("x", stripped)
        self.assertIn("y", stripped)

    def test_line_comments_are_removed(self) -> None:
        source = "value = true -- ? postulate\nnext = false\n"
        stripped = AUDIT.strip_agda_comments(source)
        self.assertNotIn("?", stripped)
        self.assertNotIn("postulate", stripped)
        self.assertIn("next = false", stripped)


class FindingTests(unittest.TestCase):
    def findings(self, source: str) -> list[object]:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            path = root / "Example.agda"
            path.write_text(source, encoding="utf-8")
            return AUDIT.findings_for(path, source, root)

    def test_decidable_question_identifier_is_allowed(self) -> None:
        findings = self.findings("module Example where\nopen X using (_≤?_)\n")
        self.assertEqual(findings, [])

    def test_standalone_question_metavariable_is_rejected(self) -> None:
        findings = self.findings("module Example where\nvalue = ?\n")
        self.assertEqual(
            [finding.kind for finding in findings],
            ["standalone_question_metavariable"],
        )

    def test_commented_postulate_is_allowed(self) -> None:
        findings = self.findings(
            "module Example where\n-- postulate hidden : Set\nvalue = true\n"
        )
        self.assertEqual(findings, [])

    def test_code_postulate_is_rejected(self) -> None:
        findings = self.findings(
            "module Example where\npostulate\n  hidden : Set\n"
        )
        self.assertEqual([finding.kind for finding in findings], ["postulate"])

    def test_allow_unsolved_metas_option_is_rejected(self) -> None:
        findings = self.findings(
            "{-# OPTIONS --allow-unsolved-metas #-}\nmodule Example where\n"
        )
        self.assertEqual([finding.kind for finding in findings], ["unsolved_metas"])

    def test_unsafe_option_is_rejected(self) -> None:
        findings = self.findings(
            "{-# OPTIONS --unsafe #-}\nmodule Example where\n"
        )
        self.assertEqual([finding.kind for finding in findings], ["unsafe"])


if __name__ == "__main__":
    unittest.main()
