#!/usr/bin/env python3
"""Offline checker-runner receipts are observations, not kernel certificates."""
from __future__ import annotations
from hashlib import sha256
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
from lean_world_builder_contract import PendingExport
from lean_world_external_checker import check_native_export, CheckerError


class ExternalCheckerTests(unittest.TestCase):
    def setUp(self):
        self.raw = b'{"meta":{"format":{"version":"3.0"}}}\n{"thm":{}}\n'
        self.export = PendingExport(
            "a"*64, sha256(self.raw).hexdigest(), self.raw, "r/r",
            "b"*40, "A", "A.foo", "lean4-pin", "closure",
            (("A.lean", "c"*64),))
        self.executable = Path(sys.executable).resolve()
        self.pin = sha256(self.executable.read_bytes()).hexdigest()

    def run_checker(self, program, **kwargs):
        return check_native_export(
            self.export, self.executable,
            expected_executable_sha256=self.pin,
            arguments=("-c", program), **kwargs)

    def test_exit_zero_is_only_external_observation(self):
        result = self.run_checker("import sys; assert sys.argv[-1].endswith('.ndjson')")
        self.assertEqual(result.artifact_sha256, self.export.artifact_sha256)
        self.assertEqual(result.executable_sha256, self.pin)
        self.assertEqual(result.status, "external-checker-exit-zero-uncertified")
        self.assertFalse(result.kernel_certified)
        self.assertFalse(result.world_admitted)

    def test_reject_nonzero(self):
        with self.assertRaisesRegex(CheckerError, "rejected"):
            self.run_checker("import sys; sys.exit(3)")

    def test_reject_bad_binary_pin_before_execution(self):
        with self.assertRaisesRegex(CheckerError, "pin mismatch"):
            check_native_export(self.export, self.executable,
                                expected_executable_sha256="f"*64)

    def test_reject_changed_artifact(self):
        invalid = PendingExport(
            self.export.handoff_key, self.export.artifact_sha256, b"tampered",
            self.export.repository, self.export.revision, self.export.module,
            self.export.declaration, self.export.toolchain,
            self.export.dependency_closure_id, self.export.source_closure)
        with self.assertRaisesRegex(CheckerError, "identity mismatch"):
            check_native_export(invalid, self.executable,
                                expected_executable_sha256=self.pin)

    def test_reject_mutating_checker(self):
        with self.assertRaisesRegex(CheckerError, "modified"):
            self.run_checker(
                "import sys,pathlib; pathlib.Path(sys.argv[-1]).write_bytes(b'bad')")

    def test_timeout_does_not_count_as_check(self):
        with self.assertRaisesRegex(CheckerError, "timed out"):
            self.run_checker("import time; time.sleep(4)", timeout=1)

    def test_zero_output_budget_keeps_silent_rejection_distinct(self):
        with self.assertRaisesRegex(CheckerError, "rejected"):
            self.run_checker("import sys; sys.exit(7)", max_output_bytes=0)

    def test_nonempty_output_respects_cap(self):
        with self.assertRaisesRegex(CheckerError, "output exceeded"):
            self.run_checker("print('x'*100)", max_output_bytes=10)


if __name__ == "__main__":
    unittest.main()
