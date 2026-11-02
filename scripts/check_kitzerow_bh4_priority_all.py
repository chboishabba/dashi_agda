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
    "check_bh4_state_payment_acquisition.py",
    "check_bh4_pathway_ontology.py",
    "check_bh4_pathway_review.py",
    "check_kitzerow_primary_chart.py",
    "check_kitzerow_chart_source_text.py",
    "check_kitzerow_source_chart_acquisition.py",
    "check_bh4_numeric_flux_guard.py",
    "check_bh4_exchange_identifiability.py",
]:
    runpy.run_path(str(root / "scripts" / name), run_name="__main__")
print("Kitzerow BH4 aggregate evidence + identity + chemistry + executed-panel + quantitative + flux-ranking + payment-preparation + state-acquisition + ontology + source-reopening review Phase-4 regression: ok")
