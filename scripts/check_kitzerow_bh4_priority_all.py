#!/usr/bin/env python3
"""Run the legacy #1159 and all focused Phase-4 regressions."""
from pathlib import Path
import runpy
root = Path(__file__).resolve().parents[1]
for name in [
    "check_kitzerow_bh4_priority.py",
    "check_bh4_phase4_system_state.py",
    "check_bh4_phase4_quantitative.py",
    "check_bh4_flux_candidate_ranking.py",
    "check_bh4_flux_payment_preparation.py",
]:
    runpy.run_path(str(root / "scripts" / name), run_name="__main__")
print("Kitzerow BH4 aggregate evidence + identity + chemistry + executed-panel + quantitative + flux-ranking + payment-preparation Phase-4 regression: ok")
