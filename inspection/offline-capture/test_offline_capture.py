#!/usr/bin/env python3
"""Deterministic regression tests for the offline-capture leaf."""

from __future__ import annotations

import importlib.util
import json
import os
import tempfile
import unittest
from pathlib import Path


MODULE_PATH = Path(__file__).with_name("offline_capture.py")
SPEC = importlib.util.spec_from_file_location("offline_capture", MODULE_PATH)
assert SPEC is not None and SPEC.loader is not None
offline_capture = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(offline_capture)


class OfflineCaptureTests(unittest.TestCase):
    def _source_tree(self, root: Path) -> Path:
        source = root / "source"
        (source / "nested").mkdir(parents=True)
        (source / "alpha.txt").write_bytes(b"alpha\n")
        (source / "nested" / "beta.bin").write_bytes(bytes(range(32)))
        return source

    def test_capture_is_deterministic_for_same_bytes_and_label(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            source = self._source_tree(root)

            first = root / "capture-a"
            second = root / "capture-b"

            manifest_a = offline_capture.capture(source, first, "field-run-001")
            manifest_b = offline_capture.capture(source, second, "field-run-001")

            self.assertEqual(manifest_a, manifest_b)
            self.assertEqual(
                (first / "manifest.json").read_bytes(),
                (second / "manifest.json").read_bytes(),
            )
            self.assertEqual(
                offline_capture.verify(first),
                offline_capture.verify(second),
            )

    def test_capture_preserves_file_bytes_and_sorted_paths(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            source = self._source_tree(root)
            capture_dir = root / "capture"

            manifest = offline_capture.capture(source, capture_dir, "field-run-002")

            paths = [entry["path"] for entry in manifest["files"]]
            self.assertEqual(paths, ["alpha.txt", "nested/beta.bin"])
            self.assertEqual(
                (capture_dir / "payload" / "alpha.txt").read_bytes(),
                b"alpha\n",
            )
            self.assertEqual(
                (capture_dir / "payload" / "nested" / "beta.bin").read_bytes(),
                bytes(range(32)),
            )

    def test_single_file_capture_uses_basename(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            source = root / "sample.dat"
            source.write_bytes(b"sample")
            capture_dir = root / "capture"

            manifest = offline_capture.capture(source, capture_dir, "single-file")

            self.assertEqual(len(manifest["files"]), 1)
            self.assertEqual(manifest["files"][0]["path"], "sample.dat")
            self.assertEqual(offline_capture.verify(capture_dir), manifest)

    def test_tampered_payload_fails_verification(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            source = self._source_tree(root)
            capture_dir = root / "capture"
            offline_capture.capture(source, capture_dir, "field-run-003")

            (capture_dir / "payload" / "alpha.txt").write_bytes(b"tampered\n")

            with self.assertRaises(offline_capture.CaptureError):
                offline_capture.verify(capture_dir)

    def test_extra_payload_file_fails_verification(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            source = self._source_tree(root)
            capture_dir = root / "capture"
            offline_capture.capture(source, capture_dir, "field-run-004")

            (capture_dir / "payload" / "extra.txt").write_text(
                "unexpected", encoding="utf-8"
            )

            with self.assertRaises(offline_capture.CaptureError):
                offline_capture.verify(capture_dir)

    def test_manifest_entry_reordering_fails_verification(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            source = self._source_tree(root)
            capture_dir = root / "capture"
            offline_capture.capture(source, capture_dir, "field-run-005")

            manifest_path = capture_dir / "manifest.json"
            manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
            manifest["files"].reverse()
            manifest_path.write_text(
                json.dumps(manifest, sort_keys=True, indent=2) + "\n",
                encoding="utf-8",
            )

            with self.assertRaises(offline_capture.CaptureError):
                offline_capture.verify(capture_dir)

    def test_destination_inside_source_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            source = self._source_tree(root)

            with self.assertRaises(offline_capture.CaptureError):
                offline_capture.capture(
                    source,
                    source / "capture",
                    "field-run-006",
                )

    @unittest.skipUnless(hasattr(os, "symlink"), "platform does not support symlinks")
    def test_symlink_source_entry_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            source = self._source_tree(root)
            link = source / "link.txt"
            try:
                link.symlink_to(source / "alpha.txt")
            except (OSError, NotImplementedError):
                self.skipTest("symlink creation is not permitted")

            with self.assertRaises(offline_capture.CaptureError):
                offline_capture.capture(source, root / "capture", "field-run-007")


if __name__ == "__main__":
    unittest.main(verbosity=2)
