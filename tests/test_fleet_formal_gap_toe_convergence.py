from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

PRODUCTION = ROOT / "DASHI/Unified/FleetFormalGapTOEExact.agda"
REGRESSION = ROOT / "DASHI/Unified/FleetFormalGapTOERegression.agda"
TOE = ROOT / "DASHI/EverythingTOESymmetryResolved369.agda"
UNIFIER = ROOT / "DASHI/Unifier.agda"
EVERYTHING = ROOT / "DASHI/Unified/Everything.agda"

def combined() -> str:
    return "\n".join(
        p.read_text(encoding="utf-8")
        for p in (PRODUCTION, REGRESSION, TOE, UNIFIER, EVERYTHING)
    )

def test_fleet_58_gap_surface_is_connected():
    text = combined()
    required = [
        "canonicalFleetFormalGapReceipt",
        "dischargedCoreKnowledgeCount",
        "polarityContradictionCount",
        "unformalisedFormalGapCount",
        "dispatchAllowed",
        "spectralMotifDoesNotCreateTruth",
        "formalGapCountDoesNotCreateProof",
        "canonicalLegalGovernanceHandoff",
        "toeFleetFormalGapReceipt",
        "unifierFleetFormalGapReceipt",
        "DASHI.Unified.FleetFormalGapTOERegression",
    ]
    missing = [name for name in required if name not in text]
    assert not missing, missing

def test_fleet_counts_are_exact_source_receipts():
    text = PRODUCTION.read_text(encoding="utf-8")
    for literal in ["584", "44", "58", "74.5526", "18.8350", "5.5865",
                    "itir.pnf.spectral_numeric_abi.v0_2"]:
        assert literal in text

def test_no_forbidden_trust_escape_or_esd_mutation_text():
    text = combined()
    forbidden = [
        "postulate",
        "allow-unsolved-metas",
        "{-# TERMINATING #-}",
        "{-# NO_POSITIVITY_CHECK #-}",
    ]
    for marker in forbidden:
        assert marker not in text
