from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
UNIFIED = ROOT / "DASHI" / "Unified"
TOE = ROOT / "DASHI" / "EverythingTOESymmetryResolved369.agda"
UNIFIER = ROOT / "DASHI" / "Unifier.agda"
EVERYTHING = UNIFIED / "Everything.agda"

def read(path: Path) -> str:
    assert path.is_file(), f"missing {path.relative_to(ROOT)}"
    return path.read_text(encoding="utf-8")

def test_dual_58_receipt_preserves_distinct_authorities() -> None:
    fleet = read(UNIFIED / "FleetFormalGapTargetTOEExact.agda")
    owner = read(UNIFIED / "BalabanFleetDual58TOEExact.agda")
    validation = read(UNIFIED / "BalabanFleetDual58TOEValidation.agda")

    for marker in (
        "dischargedCoreKnowledgeFibres",
        "584",
        "unformalisedFormalGaps",
        "58",
        "lambda1=74.5526",
        "lambda2=18.8350",
        "lambda3=5.5865",
        "fleetEigenPriorityDoesNotCreateProof",
    ):
        assert marker in fleet

    for marker in (
        "canonicalBalabanRGTOEReceipt",
        "canonicalGovernanceBalabanIbrahim58GapTOEReceipt",
        "canonicalFleetFormalGapTargetReceipt",
        "fleetFormalGapCountIs58",
        "gate4GapCountIs58",
        "fleetDischargedFibresIs584",
        "fleetContradictionGapsIs44",
        "equal58CardinalityDoesNotCreateSameObject",
        "finiteRGDoesNotPromoteContinuum",
    ):
        assert marker in owner

    for marker in (
        "rootReceiptMatchesOwner",
        "unifierReceiptMatchesOwner",
        "unifiedReceiptMatchesOwner",
        "fleet58RemainsFleet58",
        "gate458RemainsGate458",
    ):
        assert marker in validation

def test_dual_58_owner_is_reachable_from_all_toe_facades() -> None:
    required = "DASHI.Unified.BalabanFleetDual58TOEExact"
    assert required in read(TOE)
    assert required in read(UNIFIER)
    assert required in read(EVERYTHING)

def test_no_esd_or_trust_escape_is_introduced_by_dual_58_surface() -> None:
    text = read(UNIFIED / "BalabanFleetDual58TOEExact.agda")
    forbidden = ("postulate", "allow-unsolved-metas", "TERMINATING", "NO_POSITIVITY_CHECK")
    for token in forbidden:
        assert token not in text
    assert "digital_esd" not in text.lower()
    assert "import DASHI.ESD" not in text
