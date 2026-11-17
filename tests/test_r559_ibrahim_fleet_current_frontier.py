from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
UNIFIED = ROOT / "DASHI" / "Unified"
TOE = ROOT / "DASHI" / "EverythingTOESymmetryResolved369.agda"
UNIFIER = ROOT / "DASHI" / "Unifier.agda"
EVERYTHING = UNIFIED / "Everything.agda"

def read(path: Path) -> str:
    assert path.is_file(), f"missing {path.relative_to(ROOT)}"
    return path.read_text(encoding="utf-8")

def test_current_frontier_and_typed_continuum_no_go_are_reused() -> None:
    owner = read(UNIFIED / "R559IbrahimFleetHyperfabricTOEExact.agda")
    for marker in (
        "YMBalabanContinuumLimitReceipt",
        "YMDepthAsContinuumLimitReceipt",
        "BalabanClayGate4CurrentFrontierReceipt",
        "toeBalabanContinuumPromotionImpossible",
        "toeDepthContinuumPromotionImpossible",
        "currentGate4FrontierLedgerLevel",
        "currentGate4ClusteringToTransferGapLevel",
        "fleetFormalGapTargetSelected = true",
        "historicalGate4CountSelectedAsFleetTarget = false",
        "fleetGate4EqualCardinalityDoesNotSelectCanonicalMap",
    ):
        assert marker in owner

def test_all_toe_facades_reach_the_current_frontier_boundary() -> None:
    for path, prefix in (
        (TOE, "toe"),
        (UNIFIER, "unifier"),
        (EVERYTHING, "unified"),
    ):
        text = read(path)
        for suffix in (
            "BalabanContinuumPromotionImpossible",
            "DepthContinuumPromotionImpossible",
            "CurrentGate4FrontierLedgerLevel",
            "CurrentGate4ClusteringToTransferGapLevel",
            "FleetFormalGapTargetSelected",
            "HistoricalGate4CountSelectedAsFleetTarget",
        ):
            assert f"{prefix}{suffix}" in text

def test_validation_binds_facades_to_owner() -> None:
    text = read(UNIFIED / "R559IbrahimFleetHyperfabricTOEValidation.agda")
    for marker in (
        "toeCurrentGate4FrontierMatchesOwner",
        "unifierCurrentGate4FrontierMatchesOwner",
        "unifiedCurrentGate4FrontierMatchesOwner",
        "toeFleetTargetSelectionMatchesOwner",
        "unifierFleetTargetSelectionMatchesOwner",
        "unifiedFleetTargetSelectionMatchesOwner",
    ):
        assert marker in text

def test_no_trust_escape_or_esd_dependency_in_extended_owner() -> None:
    text = read(UNIFIED / "R559IbrahimFleetHyperfabricTOEExact.agda")
    for token in ("postulate", "allow-unsolved-metas", "TERMINATING", "NON_TERMINATING", "NO_POSITIVITY_CHECK", "{!!}"):
        assert token not in text
    assert "digital_esd" not in text.lower()
    assert "import DASHI.ESD" not in text
