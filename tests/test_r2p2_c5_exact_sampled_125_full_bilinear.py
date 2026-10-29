"""Regression for exact C5 all-output sampled Fourier quadratic arithmetic."""
import runpy
from pathlib import Path


def test_full_c5_125_sampled_bilinear():
    path = Path(__file__).resolve().parents[1] / "scripts" / "r2p2_c5_exact_sampled_125_full_bilinear.py"
    runpy.run_path(str(path))["check"]()
