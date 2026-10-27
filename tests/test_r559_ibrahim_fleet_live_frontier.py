from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
UNIFIED = ROOT / "DASHI" / "Unified"
TOE = ROOT / "DASHI" / "EverythingTOESymmetryResolved369.agda"
UNIFIER = ROOT / "DASHI" / "Unifier.agda"
EVERYTHING = UNIFIED / "Everything.agda"

def read(path: Path) -> str:
    assert path.is_file(), f"missing {path.relative_to(ROOT)}"
    return path.read_text(encoding="utf-8")

def test_joint_owner_reuses_canonical_continuum_and_live_frontier_owners() -> None:
    owner = read(UNIFIED / "R559IbrahimFleetHyperfabricTOEExact.agda")
    for marker in (
        "import DASHI.Unified.BalabanRGTOERegression as Balaban",
        "BalabanClayGate4CurrentFrontierReceipt",
        "EqualCardinalityStructureBoundaryExact",
        "Balaban.BalabanContinuumLimitPromotion",
        "Balaban.DepthContinuumLimitPromotion",
        "currentGate4FrontierLedgerLevel",
        "currentGate4ClusteringToTransferGapLevel",
        "fleetFormalGapTargetSelected = true",
        "historicalGate4CountSelectedAsFleetTarget = false",
        "fleetGate4EqualCardinalityDoesNotSelectCanonicalMap",
    ):
        assert marker in owner
    assert "import DASHI.Physics.Closure.YMBalabanContinuumLimitReceipt" not in owner
    assert "import DASHI.Physics.Closure.YMDepthAsContinuumLimitReceipt" not in owner

def test_current_frontier_and_target_split_reach_all_three_facades() -> None:
    for path, prefix in (
        (TOE, "toe"),
        (UNIFIER, "unifier"),
        (EVERYTHING, "unified"),
    ):
        text = read(path)
        for suffix in (
            "CurrentGate4FrontierLedgerLevel",
            "CurrentGate4ClusteringToTransferGapLevel",
            "FleetFormalGapTargetSelected",
            "HistoricalGate4CountSelectedAsFleetTarget",
            "FleetGate4EqualCardinalityDoesNotSelectCanonicalMap",
        ):
            assert f"{prefix}{suffix}" in text

def test_typed_continuum_no_go_is_reused_not_reinvented() -> None:
    assert "toeBalabanContinuumLimitPromotionImpossible" in read(TOE)
    assert "toeDepthContinuumLimitPromotionImpossible" in read(TOE)
    assert "unifierBalabanContinuumLimitPromotionImpossible" in read(UNIFIER)
    assert "unifierDepthContinuumLimitPromotionImpossible" in read(UNIFIER)

    unified = read(EVERYTHING)
    assert "unifiedBalabanContinuumLimitPromotionImpossible" in unified
    assert "unifiedDepthContinuumLimitPromotionImpossible" in unified

def test_validation_binds_live_frontier_and_no_go_to_canonical_owners() -> None:
    text = read(UNIFIED / "R559IbrahimFleetHyperfabricTOEValidation.agda")
    for marker in (
        "toeCurrentGate4FrontierMatchesOwner",
        "unifierCurrentGate4FrontierMatchesOwner",
        "unifiedCurrentGate4FrontierMatchesOwner",
        "toeFleetTargetSelectionMatchesOwner",
        "unifierFleetTargetSelectionMatchesOwner",
        "unifiedFleetTargetSelectionMatchesOwner",
        "rootBalabanContinuumNoGoReachable",
        "unifierBalabanContinuumNoGoReachable",
        "unifiedBalabanContinuumNoGoReachable",
    ):
        assert marker in text

def test_no_trust_escape_or_esd_dependency_in_joint_owner() -> None:
    text = read(UNIFIED / "R559IbrahimFleetHyperfabricTOEExact.agda")
    for token in (
        "postulate",
        "allow-unsolved-metas",
        "TERMINATING",
        "NON_TERMINATING",
        "NO_POSITIVITY_CHECK",
        "{!!}",
    ):
        assert token not in text
    assert "digital_esd" not in text.lower()
    assert "import DASHI.ESD" not in text
