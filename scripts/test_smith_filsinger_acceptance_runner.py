"""Synthetic temporary Git repos test the shell receipt guard, NOT Agda itself."""
import pathlib
import shutil
import subprocess
import tempfile
import unittest

RUNNER = pathlib.Path(__file__).with_name("run_smith_filsinger_acceptance.sh")
SUITES = ("original_gate_evidence", "signed_vi_intervals",
          "restored_cycle_intervals", "restored_cycle_raw_replay")


class AcceptanceRunnerControlTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = pathlib.Path(self.tmp.name)
        (self.root / "scripts").mkdir()
        shutil.copyfile(RUNNER, self.root / "scripts" / RUNNER.name)
        for suite in SUITES:
            (self.root / "scripts" / ("test_smith_filsinger_" + suite + ".py")).write_text(
                "import sys\nsys.exit(0)\n"
            )
        self.git("init", "-q")
        self.git("config", "user.email", "test@example.com")
        self.git("config", "user.name", "Test")
        self.git("add", ".")
        self.git("commit", "-qm", "synthetic fixture")

    def git(self, *args):
        subprocess.run(["git", *args], cwd=self.root, check=True,
                       stdout=subprocess.PIPE, stderr=subprocess.PIPE)

    def run_acceptance(self, mode="--python-only"):
        return subprocess.run(
            ["bash", "scripts/" + RUNNER.name, mode], cwd=self.root,
            capture_output=True, text=True,
        )

    @property
    def receipt(self):
        return self.root / ".filsinger-acceptance" / "acceptance-pass.txt"

    def test_clean_python_only_is_not_kernel(self):
        p = self.run_acceptance()
        self.assertEqual(p.returncode, 0, p.stderr)
        self.assertIn("PYTHON_ONLY_NO_AGDA_ACCEPTANCE", self.receipt.read_text())

    def test_dirty_tracked_source_deletes_previous_receipt(self):
        self.assertEqual(self.run_acceptance().returncode, 0)
        (self.root / "scripts/test_smith_filsinger_original_gate_evidence.py").write_text("raise Exception('changed')\n")
        self.assertNotEqual(self.run_acceptance().returncode, 0)
        self.assertFalse(self.receipt.exists())

    def test_untracked_agda_source_deletes_previous_receipt(self):
        self.assertEqual(self.run_acceptance().returncode, 0)
        (self.root / "DASHI").mkdir()
        (self.root / "DASHI/Untracked.agda").write_text("module Untracked where\n")
        self.assertNotEqual(self.run_acceptance().returncode, 0)
        self.assertFalse(self.receipt.exists())

    def test_failing_committed_python_script_has_no_receipt(self):
        (self.root / "scripts/test_smith_filsinger_original_gate_evidence.py").write_text(
            "import sys\nsys.exit(12)\n"
        )
        self.git("add", ".")
        self.git("commit", "-qm", "synthetic failing suite")
        self.assertNotEqual(self.run_acceptance().returncode, 0)
        self.assertFalse(self.receipt.exists())

    def test_no_agda_checker_cannot_earn_full_receipt(self):
        self.assertNotEqual(self.run_acceptance("--full").returncode, 0)
        self.assertFalse(self.receipt.exists())

    def test_second_run_ignores_generated_agdai(self):
        self.assertEqual(self.run_acceptance().returncode, 0)
        (self.root / "DASHI").mkdir()
        (self.root / "DASHI/cache.agdai").write_text("cache")
        p = self.run_acceptance()
        self.assertEqual(p.returncode, 0, p.stderr)


if __name__ == "__main__":
    unittest.main()
