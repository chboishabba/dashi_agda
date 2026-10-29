"""Q(i) C4 sampled-field quadratic regression (not an Agda type-check)."""
import runpy
from pathlib import Path


def test_c4_sampled_quadratic_exact():
    script = Path(__file__).resolve().parents[1] / "scripts" / "r2p2_c4_3d_exact_sampled_quadratic_dft.py"
    runpy.run_path(str(script))["check"]()
