from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def text(path: str) -> str:
    return (ROOT / path).read_text(encoding="utf-8")


def test_holographic_receipt_keeps_continuum_yang_mills_fail_closed():
    p = text("DASHI/Physics/Closure/HolographicBulkBoundaryReceipt.agda")
    assert "continuumYangMillsConstructedIsFalse" in p
    assert "continuumYangMillsConstructed ≡ false" in p
    assert "; continuumYangMillsConstructed =\n        false" in p


def test_holographic_receipt_boundary_matches_boolean_status():
    p = text("DASHI/Physics/Closure/HolographicBulkBoundaryReceipt.agda")
    assert "No Clay Yang-Mills, continuum Yang-Mills, or terminal Clay claim is promoted" in p
