#!/usr/bin/env python3
"""Deterministic no-network negative controls for Bishop source closure."""
import subprocess
import tempfile
from pathlib import Path
from check_bishop_cross_pr_dependency_closure import closure, stage, Blocked


def main():
    with tempfile.TemporaryDirectory() as temporary:
        root = Path(temporary)
        repo = root / "r"
        repo.mkdir()
        def git(*args):
            return subprocess.check_output(
                ["git", "-C", str(repo), *args], text=True).strip()
        git("init", "-q")
        git("config", "user.email", "proof-test@example.invalid")
        git("config", "user.name", "Proof Closure Test")
        dashi = repo / "DASHI"
        dashi.mkdir()
        (dashi / "Common.agda").write_text("module DASHI.Common where\n")
        git("add", ".")
        git("commit", "-qm", "base")
        baseline = git("rev-parse", "HEAD")

        (dashi / "Intermediate.agda").write_text(
            "module DASHI.Intermediate where\nimport DASHI.Common as C\n")
        (dashi / "Root.agda").write_text(
            "module DASHI.Root where\nopen import DASHI.Intermediate\n")
        git("add", ".")
        git("commit", "-qm", "donor")
        donor = git("rev-parse", "HEAD")
        result = closure(repo, baseline, donor, ["DASHI/Root.agda"])
        assert result["counts"] == {
            "BASELINE": 1, "DONOR_TRANSFER": 2, "UNRESOLVED": 0}
        assert result["dashi_imports_closed"]
        assert not result["kernel_accepted"]

        target = root / "stage"
        stage(repo, donor, result, target)
        assert (target / "DASHI/Root.agda").exists()
        assert (target / "DASHI/Intermediate.agda").exists()
        assert not (target / "DASHI/Common.agda").exists()
        try:
            stage(repo, donor, result, target)
        except Blocked:
            pass
        else:
            raise AssertionError("refused-to-overwrite gate failed")

        (dashi / "Broken.agda").write_text(
            "module DASHI.Broken where\nimport DASHI.Absent\n")
        git("add", ".")
        git("commit", "-qm", "broken")
        broken = git("rev-parse", "HEAD")
        bad = closure(repo, baseline, broken, ["DASHI/Broken.agda"])
        assert bad["counts"]["UNRESOLVED"] == 1
        try:
            stage(repo, broken, bad, root / "bad-stage")
        except Blocked:
            pass
        else:
            raise AssertionError("unresolved-import staging gate failed")
        print("PASS: recursive import closure, donor staging, overwrite and missing-import negative tests")
        print("NO Agda/Lean kernel receipt or mathematical gate acceptance")


if __name__ == "__main__":
    main()
