#!/usr/bin/env python3
from __future__ import annotations

import importlib.util
import pathlib
import unittest

HERE = pathlib.Path(__file__).resolve().parent
CHECKER = HERE / "check_agda_static.py"

spec = importlib.util.spec_from_file_location("check_agda_static", CHECKER)
assert spec is not None and spec.loader is not None
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)


class LexicalStructureTests(unittest.TestCase):
    def test_balanced_module(self) -> None:
        text = "module DASHI.X where\nfoo : Set\nfoo = Set\n"
        self.assertEqual(module.scan_lexical_structure(text), [])

    def test_nested_block_comments(self) -> None:
        text = "module DASHI.X where\n{- outer {- inner -} outer -}\nfoo = Set\n"
        self.assertEqual(module.scan_lexical_structure(text), [])

    def test_string_delimiters_ignored(self) -> None:
        text = 'module DASHI.X where\nfoo = "([{ not syntax }])"\n'
        self.assertEqual(module.scan_lexical_structure(text), [])

    def test_unclosed_delimiter_detected(self) -> None:
        errors = module.scan_lexical_structure("module DASHI.X where\nfoo = (\n")
        self.assertTrue(any("unclosed delimiter" in error for error in errors))

    def test_unterminated_block_comment_detected(self) -> None:
        errors = module.scan_lexical_structure("module DASHI.X where\n{- open\n")
        self.assertTrue(any("unterminated nested block comment" in error for error in errors))

    def test_unterminated_string_detected(self) -> None:
        errors = module.scan_lexical_structure('module DASHI.X where\nfoo = "open\n')
        self.assertTrue(any("unterminated string literal" in error for error in errors))


class ModulePathTests(unittest.TestCase):
    def test_expected_module_from_path(self) -> None:
        root = pathlib.Path("/tmp/repo")
        path = root / "DASHI" / "Education" / "Example.agda"
        self.assertEqual(
            module.expected_module_for(path, root),
            "DASHI.Education.Example",
        )


if __name__ == "__main__":
    unittest.main()
