"""Run the exact finite character-basis certificate on source checkout."""
import runpy
from pathlib import Path


def test_universal_quadratic_dft_basis_certificate():
    src = Path(__file__).resolve().parents[1] / "scripts" / "r2p2_c4_c5_universal_basis_certificate.py"
    runpy.run_path(str(src))["certificate"]()
