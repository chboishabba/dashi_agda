#!/usr/bin/env python3
"""Offline Rust nanoda checker interface and independent axiom policy tests."""
from __future__ import annotations
from hashlib import sha256
from pathlib import Path
import json
import sys
import tempfile
import unittest

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/"scripts"))
from lean_world_builder_contract import PendingExport
from lean_world_external_checker import check_native_export_nanoda, CheckerError
from run_lean_world_real_semantic_acceptance import (
    nanoda_policy,replace_theorem_proof_with_type,AcceptanceError)


class RustNanodaInterface(unittest.TestCase):
    def setUp(self):
        self.t=tempfile.TemporaryDirectory()
        self.addCleanup(self.t.cleanup)
        self.root=Path(self.t.name)
        raw=b'{"meta":{"format":{"version":"3.1.0"}}}\n{"thm":{"type":1,"value":2}}\n'
        self.export=PendingExport(
            "a"*64,sha256(raw).hexdigest(),raw,"org/repo","b"*40,
            "Target","Demo","lean4-4.28.0","closure",
            (("Target.lean","c"*64),))

    def checker(self, body):
        exe=self.root/"fake-nanoda"
        exe.write_text("#!"+sys.executable+"\n"+body+"\n")
        exe.chmod(0o700)
        return exe,sha256(exe.read_bytes()).hexdigest()

    def run_mock(self,body):
        exe,pin=self.checker(body)
        return check_native_export_nanoda(
            self.export,exe,expected_executable_sha256=pin)

    def test_strict_axioms_and_no_dotnet_requirement(self):
        p=nanoda_policy()
        self.assertNotIn("sorryAx",p["permitted_axioms"])
        self.assertFalse(p["unsafe_permit_all_axioms"])
        self.assertFalse(p["unpermitted_axiom_hard_error"])
        self.assertEqual(p["permitted_axioms"],
                         ["propext","Classical.choice",
                          "Quot.sound","Lean.trustCompiler"])

    def test_config_is_real_nanoda_json_interface(self):
        receipt=self.run_mock(
            "import json,sys,pathlib\n"
            "cfg=json.load(open(sys.argv[1]))\n"
            "assert cfg['export_file_path'].endswith('.ndjson')\n"
            "assert not cfg['unsafe_permit_all_axioms']\n"
            "assert not cfg['use_stdin']\n"
            "assert pathlib.Path(cfg['export_file_path']).exists()\n"
            "print('Checked 2 declarations with no errors')")
        self.assertFalse(receipt.kernel_certified)
        self.assertFalse(receipt.world_admitted)
        self.assertEqual(receipt.status,"external-checker-exit-zero-uncertified")

    def test_checker_rejects_nonzero_and_empty_success(self):
        with self.assertRaisesRegex(CheckerError,"rejected"):
            self.run_mock("raise SystemExit(4)")
        with self.assertRaisesRegex(CheckerError,"no explicit"):
            self.run_mock("pass")

    def test_wrong_binary_pin_rejected(self):
        exe,pin=self.checker("print('Checked 2 declarations with no errors')")
        with self.assertRaisesRegex(CheckerError,"pin mismatch"):
            check_native_export_nanoda(
                self.export,exe,expected_executable_sha256="0"*64)

    def test_semantic_negative_control_changes_proof_not_syntax(self):
        source=(
            b'{"meta":{"format":{"version":"3.1.0"}}}\n'
            b'{"thm":{"name":1,"type":2,"value":3}}\n')
        bad=replace_theorem_proof_with_type(source)
        row=json.loads(bad.splitlines()[1])
        self.assertEqual(row["thm"]["value"],row["thm"]["type"])
        self.assertNotEqual(source,bad)

    def test_negative_control_rejects_no_distinct_proof(self):
        with self.assertRaises(AcceptanceError):
            replace_theorem_proof_with_type(
                b'{"meta":{"format":{"version":"3.1.0"}}}\n'
                b'{"thm":{"name":1,"type":2,"value":2}}\n')


if __name__=="__main__":
    unittest.main()
