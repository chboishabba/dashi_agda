#!/usr/bin/env python3
"""Regression: Karp21 referee preflight works without Agda; proof modes fail closed.

Uses an isolated PATH containing Python, dirname and a fake git revision.
The preflight checkers are harmless fixture stubs so the test checks
referee control flow independently of the actual mathematical fixtures.
This is NOT an Agda kernel receipt or a replacement for any regression.
"""
from __future__ import annotations

import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

CHECKERS = (
    "check_karp21_reserved_formula_constructors.py",
    "check_karp21_tape_boundary_ghost.py",
    "check_karp21_tape_guarded_uniqueness_small.py",
    "check_karp21_agda_stdlib_arity.py",
    "check_karp21_e20_bitlength_bound.py",
    "check_karp_binary_codec.py",
    "check_karp21_binary_native_sparse_verifier.py",
)


def check(referee: Path) -> None:
    with tempfile.TemporaryDirectory(prefix="karp21-referee-test-") as dirname:
        repo = Path(dirname)
        scripts = repo / "scripts"
        scripts.mkdir()
        shutil.copyfile(referee, scripts / referee.name)
        calls = scripts / "called.txt"
        for checker in CHECKERS:
            (scripts / checker).write_text(
                "from pathlib import Path\n"
                f"with (Path(__file__).parent / 'called.txt').open('a') as out: out.write('{checker}\\n')\n",
                encoding="utf8",
            )
        bin_dir = repo / "isolated-bin"
        bin_dir.mkdir()
        python = bin_dir / "python3"
        python.symlink_to(sys.executable)
        external_dirname = shutil.which("dirname")
        assert external_dirname is not None
        (bin_dir / "dirname").symlink_to(external_dirname)
        git = bin_dir / "git"
        git.write_text("#!/bin/sh\nprintf 'fixture-sha\\n'\n", encoding="utf8")
        git.chmod(0o755)
        assert not (bin_dir / "agda").exists()
        env = dict(os.environ, PATH=str(bin_dir))
        script = scripts / referee.name
        cmd = ["/bin/bash", str(script)]

        ok = subprocess.run(
            cmd + ["preflight"], cwd=repo, env=env,
            capture_output=True, text=True, check=False,
        )
        assert ok.returncode == 0, (ok.returncode, ok.stdout, ok.stderr)
        assert "Agda version: unavailable (preflight-only; no kernel receipt)" in ok.stdout
        assert "PREFLIGHT ONLY" in ok.stdout
        assert calls.read_text(encoding="utf8").splitlines() == list(CHECKERS)

        calls.unlink()
        blocked = subprocess.run(
            cmd + ["golden"], cwd=repo, env=env,
            capture_output=True, text=True, check=False,
        )
        assert blocked.returncode == 127, (blocked.returncode, blocked.stdout, blocked.stderr)
        assert "BLOCKED: agda executable unavailable" in blocked.stderr
        assert not calls.exists(), "The kernel mode ran preflights without Agda"
    print("PASS: no-Agda preflight ran seven checks; golden mode rejected with exit 127")


if __name__ == "__main__":
    check(Path(__file__).with_name("referee_karp21_maxcut.sh"))
