"""Exact pair-orbit regression. This executes repository-local arithmetic, not Agda."""
import runpy
from pathlib import Path


def test_orbit365_cyclotomic_convolution():
    script = Path(__file__).resolve().parents[1] / "scripts" / "r2p2_27x27_orbit365_weighted_convolution.py"
    runpy.run_path(str(script))["check"]()
