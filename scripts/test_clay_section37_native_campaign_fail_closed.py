#!/usr/bin/env python3
"""Fail-closed tests of the ACTUAL committed all-Clay native campaign.

This does not invoke Agda/Lean, does not provide an RH source and
cannot claim any Clay theorem. It checks that a missing/incorrect
immutable owner pin or absent checkout can never yield success.
Uses the same script file, imported directly from this repository.
"""
import contextlib
import importlib.util
import inspect
import io
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

SCRIPT = Path(__file__).with_name("check_clay_section36_native_campaign.py")


def load_runner():
    spec = importlib.util.spec_from_file_location("native_campaign", SCRIPT)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


class NativeCampaignFailClosed(unittest.TestCase):
    def test_owner_pin_and_branch_contract(self):
        campaign = load_runner()
        self.assertEqual(len(campaign.BRANCHES), 5)
        self.assertEqual(
            sorted(k for k in campaign.BRANCHES),
            ["BSD_HODGE", "NS", "PNP", "RH", "YM"])
        self.assertEqual(sum(len(paths) for _, paths in
                             campaign.ROOTS.values()), 10)

    def run_campaign(self, extra_pins):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            output = root / "receipt.json"
            args = ["native", "--ym-root", str(root/"ym"),
                    "--ns-root", str(root/"ns"),
                    "--bsd-hodge-root", str(root/"bsd"),
                    "--pnp-root", str(root/"pnp"),
                    "--rh-root", str(root/"rh"),
                    "--rh-source-root", str(root/"missing_external"),
                    "--rh-manifest", str(root/"missing.json"),
                    "--rh-main-sha256", "0"*64,
                    "--rh-source-head", "0"*40,
                    "--report", str(output)] + extra_pins
            campaign = load_runner()
            with mock.patch.object(sys, "argv", args):
                with contextlib.redirect_stdout(io.StringIO()), \
                     contextlib.redirect_stderr(io.StringIO()):
                    try:
                        code = campaign.main()
                    except SystemExit as exc:
                        code = exc.code
            result = json.loads(output.read_text()) if output.exists() else None
            return code, result

    def test_missing_all_pins_rejected_before_write(self):
        code, data = self.run_campaign([])
        self.assertEqual(code, 2)
        self.assertIsNone(data)

    def test_wrong_owner_pin_rejected_before_write(self):
        code, data = self.run_campaign(
            ["--require-head", "OTHER="+"0"*40])
        self.assertEqual(code, 2)
        self.assertIsNone(data)

    def test_duplicate_owner_pin_rejected(self):
        code, data = self.run_campaign(
            ["--require-head", "YM="+"0"*40,
             "--require-head", "YM="+"0"*40])
        self.assertEqual(code, 2)
        self.assertIsNone(data)

    def test_all_pins_but_missing_worktrees_fails_closed(self):
        code, data = self.run_campaign([
            value for name in ("YM", "NS", "BSD_HODGE", "PNP", "RH")
            for value in ("--require-head", f"{name}=" + "0"*40)
        ])
        self.assertEqual(code, 2)
        self.assertFalse(data["all_selected_roots_passed"])
        self.assertEqual(set(data["roots"]),
                         {"YM", "NS", "BSD_HODGE", "PNP", "RH"})
        self.assertTrue(all(row["status"] != "PASS"
                            for row in data["checks"]))

    def test_malformed_sha_rejected_before_write(self):
        code, data = self.run_campaign(
            ["--require-head", "YM=not-a-real-commit"])
        self.assertEqual(code, 2)
        self.assertIsNone(data)

    def test_exact_ten_native_roots_plus_rh(self):
        campaign = load_runner()
        self.assertEqual(sum(len(v[1]) for v in campaign.ROOTS.values()), 10)
        self.assertIn("Clay37NativeAcceptanceV1",
                      inspect.getsource(campaign))

    def test_wrong_branch_fails_closed(self):
        campaign = load_runner()
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            for command in (["git","init","-q"],
                            ["git","checkout","-q","-b","wrong-branch"]):
                result = subprocess.run(command, cwd=root,
                                        capture_output=True, text=True)
                self.assertEqual(result.returncode, 0, result.stderr)
            identity = campaign.checkout_identity(root,
                "agent/ym-p0-cmp119-r445-master-weld-20261121")
            self.assertFalse(identity["ok"])
            self.assertEqual(identity["branch"], "wrong-branch")


if __name__ == "__main__":
    unittest.main(verbosity=2)
