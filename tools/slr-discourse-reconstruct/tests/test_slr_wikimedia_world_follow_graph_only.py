#!/usr/bin/env python3
from __future__ import annotations

import importlib.util
from pathlib import Path
import unittest

HERE = Path(__file__).resolve().parent
MODULE_PATH = HERE.parent / "slr_wikimedia_world_follow.py"
spec = importlib.util.spec_from_file_location("slr_wikimedia_world_follow", MODULE_PATH)
assert spec and spec.loader
follow = importlib.util.module_from_spec(spec)
spec.loader.exec_module(follow)


class WikimediaWorldFollowGraphOnlyTests(unittest.TestCase):
    def test_graph_only_mode_suppresses_large_model_snapshot(self) -> None:
        self.assertFalse(
            follow.should_write_output_model(
                output_model=Path("/tmp/delta-world.json"),
                graph_only=True,
            )
        )

    def test_legacy_mode_can_still_write_model_snapshot(self) -> None:
        self.assertTrue(
            follow.should_write_output_model(
                output_model=Path("/tmp/delta-world.json"),
                graph_only=False,
            )
        )

    def test_missing_output_model_is_valid_in_graph_only_mode(self) -> None:
        self.assertFalse(
            follow.should_write_output_model(
                output_model=None,
                graph_only=True,
            )
        )


if __name__ == "__main__":
    unittest.main()
