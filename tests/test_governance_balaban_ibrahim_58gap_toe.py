from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

OWNER = ROOT / "DASHI/Unified/GovernanceBalabanIbrahim58GapTOEExact.agda"
VALIDATION = ROOT / "DASHI/Unified/GovernanceBalabanIbrahim58GapTOEValidation.agda"
TOE = ROOT / "DASHI/EverythingTOESymmetryResolved369.agda"
UNIFIER = ROOT / "DASHI/Unifier.agda"
UNIFIED = ROOT / "DASHI/Unified/Everything.agda"


def read(path: Path) -> str:
    assert path.is_file(), f"missing {path.relative_to(ROOT)}"
    return path.read_text(encoding="utf-8", errors="strict")


def test_reuse_first_owners_are_explicit():
    text = read(OWNER)
    for token in (
        "GovernedLegalWorkflowTOEBridgeExact",
        "YangMillsSubmissionObligationCardinalityExact",
        "BalabanClayGate4PhysicalClosureRound6ExactCutset",
        "BalabanRGScaleTransferFrontierReceipt",
        "BalabanIbrahimParetoSnowballTOEExact",
    ):
        assert token in text


def test_exact_repo_native_58_is_gate4_only():
    text = read(OWNER)
    assert "gate4GapCountIs58" in text
    assert "Counts.gate4ObligationCount" in text
    assert "fleet584LedgerSameObjectWithGate4IsFalse" in text
    assert "Equal cardinality does not prove same object." in text


def test_fail_closed_nonpromotion_is_preserved():
    text = read(OWNER)
    for token in (
        "legalCandidateDoesNotCreateAuthority",
        "legalSystemMatchDoesNotCreateAuthority",
        "currentValidityDoesNotCreateApplicability",
        "semanticAdmissionDoesNotCreateLegalSourceAuthority",
        "documentRoleDoesNotCreateLegalSourceAuthority",
        "balabanScaleTransferPromotionImpossible",
        "ibrahimSearchPriorityDoesNotCreateProof",
        "ibrahimProducerSourceDoesNotCreateRun",
        "gate4StillConditional",
    ):
        assert token in text


def test_three_toe_facades_reach_one_receipt():
    toe = read(TOE)
    unifier = read(UNIFIER)
    unified = read(UNIFIED)
    assert "toeGovernanceBalabanIbrahim58GapReceipt" in toe
    assert "unifierGovernanceBalabanIbrahim58GapReceipt" in unifier
    assert "unifiedGovernanceBalabanIbrahim58GapReceipt" in unified
    assert "GovernanceBalabanIbrahim58GapTOEValidation" in unified


def test_validation_uses_canonical_owner():
    text = read(VALIDATION)
    for token in (
        "toeReceiptMatchesOwner",
        "unifierReceiptMatchesOwner",
        "toeGate4CountIs58",
        "unifierGate4CountIs58",
        "toeLegalCandidateStillNonPromoting",
        "toeBalabanScaleTransferStillBlocked",
        "toeIbrahimSearchPriorityStillNotProof",
        "toeIbrahimProducerStillNotExecution",
    ):
        assert token in text


def test_no_trust_escape_in_new_agda():
    forbidden = (
        "postulate",
        "allow-unsolved-metas",
        "TERMINATING",
        "NO_POSITIVITY_CHECK",
        "{!!}",
    )
    for path in (OWNER, VALIDATION):
        text = read(path)
        for token in forbidden:
            assert token not in text, f"{token} in {path.relative_to(ROOT)}"
