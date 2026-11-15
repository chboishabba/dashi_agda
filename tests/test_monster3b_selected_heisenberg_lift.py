from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

from verify_monster3b_selected_heisenberg_lift import build_receipt


def test_selected_word_has_exact_heisenberg_central_correction():
    receipt = build_receipt(ROOT)

    assert receipt["selected_word"] == "g2 g1 g2^-1 g1 g2^-1"
    assert receipt["selected_word_symplectic_multiplier"] == 1
    assert receipt["compression_matches_selected_receipt"] is True
    assert receipt["cocycle_defect_symmetric"] is True
    assert receipt["cocycle_defect_rank"] == 12
    assert receipt["quadratic_polarization_identity"] is True
    assert receipt["heisenberg_coboundary_identity"] is True
    assert receipt["central_correction_formula"] == "q(x)=2*x^T*D*x over GF(3)"
