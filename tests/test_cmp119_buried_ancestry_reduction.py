from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def read(rel: str) -> str:
    p = ROOT / rel
    assert p.is_file(), f"missing {rel}"
    return p.read_text(encoding="utf-8", errors="replace")


def test_old_section2_objects_are_definitionally_preserved_into_raw_state():
    text = read("DASHI/Physics/Foundations/GRQFTCMP119BuriedSourceAncestryReductionExact.agda")
    for token in (
        "sourceVacuumPreserved",
        "sourceEffectiveActionPreserved",
        "sourceEquation223Preserved",
        "sourceObjectsToRawStateAlreadyCompilerOwned",
        "remainingGapIsRawEq223ResponseToPinnedR136",
    ):
        assert token in text


def test_terminal_records_ancestry_reduction():
    text = read("DASHI/Physics/ExoticGravity/AntigravityABCDETerminalMaxCutExact.agda")
    assert "sourceNativeToRawAncestryClosed" in text
    assert "rawEq223ResponseToPinnedR136StillOpen" in text
