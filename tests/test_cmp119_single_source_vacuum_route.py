from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def read(rel: str) -> str:
    p = ROOT / rel
    assert p.is_file(), f"missing {rel}"
    return p.read_text(encoding="utf-8", errors="replace")


def test_one_literal_cmp119_scale_can_feed_both_static_regions():
    text = read("DASHI/Physics/Foundations/GRQFTCMP119SingleSourceVacuumKottlerRouteExact.agda")
    for token in (
        "SingleSourceVacuum",
        "sourceAmplitude",
        "singleSourceVacuumStress",
        "SingleSourceVacuumKottlerCandidate",
        "sameSourceAmplitudeFeedsInteriorExterior",
        "secondSourceVacuumScaleRequired",
    ):
        assert token in text
