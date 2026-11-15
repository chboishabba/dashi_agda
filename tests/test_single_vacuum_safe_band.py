from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def read(rel: str) -> str:
    p = ROOT / rel
    assert p.is_file(), f"missing {rel}"
    return p.read_text(encoding="utf-8", errors="replace")


def test_safe_band_reduces_israel_margins_to_one_lapse_coordinate():
    text = read("DASHI/Physics/Foundations/GRQFTSingleVacuumSafeBandExact.agda")
    for token in (
        "exteriorLapseFromInterior",
        "massFactorization",
        "outwardFactorization",
        "necDecFactorization",
        "secViolationFactorization",
        "pressureTensionFactorization",
        "safeLowerX",
        "safeUpperX",
        "sourceQSafeLower",
        "sourceQSafeUpper",
    ):
        assert token in text
