#!/usr/bin/env python3
"""Thin dashi_agda Digital-ESD delegate into the generic SLR L1->L3 runtime.

This wrapper owns no ERIC parsing, screening semantics, full-text verification,
or SLR parsing logic. It locates the SLR repository and delegates to
scripts/run_digital_esd_l1_l3.py.
"""

from __future__ import annotations

import argparse
import os
import subprocess
import sys
from pathlib import Path


def resolve_slr_root(explicit: Path | None) -> Path:
    if explicit is not None:
        root = explicit.resolve()
    elif os.environ.get("SLR_REPO_ROOT"):
        root = Path(os.environ["SLR_REPO_ROOT"]).resolve()
    else:
        candidate = (Path(__file__).resolve().parents[3] / "slr").resolve()
        if not candidate.exists():
            raise SystemExit(
                "SLR repo not found; pass --slr-root or set SLR_REPO_ROOT"
            )
        root = candidate

    driver = root / "scripts" / "run_digital_esd_l1_l3.py"
    if not driver.exists():
        raise SystemExit(f"SLR Digital-ESD driver not found: {driver}")
    return root


def main() -> int:
    parser = argparse.ArgumentParser(add_help=False)
    parser.add_argument("--slr-root", type=Path)
    known, forwarded = parser.parse_known_args()

    slr_root = resolve_slr_root(known.slr_root)
    driver = slr_root / "scripts" / "run_digital_esd_l1_l3.py"
    cmd = [sys.executable, str(driver), *forwarded]

    print("+", " ".join(cmd), file=sys.stderr)
    completed = subprocess.run(cmd, cwd=slr_root)
    return completed.returncode


if __name__ == "__main__":
    raise SystemExit(main())
