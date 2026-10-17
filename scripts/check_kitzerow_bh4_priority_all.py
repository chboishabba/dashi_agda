#!/usr/bin/env python3
"""Run the legacy #1159 regression and the Phase-4 system-state regression."""

from pathlib import Path
import runpy

root = Path(__file__).resolve().parents[1]

runpy.run_path(str(root / "scripts/check_kitzerow_bh4_priority.py"), run_name="__main__")
runpy.run_path(str(root / "scripts/check_bh4_phase4_system_state.py"), run_name="__main__")

print("Kitzerow BH4 aggregate evidence + identity + chemistry + Phase-4 system-state regression: ok")
