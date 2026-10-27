from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def read(path: str) -> str:
    return (ROOT / path).read_text(encoding="utf-8")


def test_toe_facades_reuse_same_canonical_owners() -> None:
    root = read("DASHI/EverythingTOESymmetryResolved369.agda")
    unifier = read("DASHI/Unifier.agda")
    unified = read("DASHI/Unified/Everything.agda")

    for text in (root, unifier, unified):
        assert "GovernedLegalWorkflowTOEBridgeExact" in text
        assert "BalabanIbrahimParetoSnowballTOEExact" in text
        assert "FleetFormalGapTargetTOEExact" in text

    assert "toe369GovernedLegalWorkflowAuthorityInvariantHandoff" in root
    assert "unifierGovernedLegalWorkflowAuthorityInvariantHandoff" in unifier
    assert "unifiedGovernedLegalWorkflowAuthorityInvariantHandoff" in unified


def test_fleet_target_keeps_paid_and_contradiction_fibres_out() -> None:
    fleet = read("DASHI/Unified/FleetFormalGapTargetTOEExact.agda")

    assert "13344" in fleet
    assert "584" in fleet
    assert "44" in fleet
    assert "58" in fleet
    assert "lambda1=74.5526" in fleet
    assert "lambda2=18.8350" in fleet
    assert "lambda3=5.5865" in fleet
    assert "targetOnlyUnformalisedFormalGaps" in fleet
    assert "fleetDischargedFibresCannotBeRetargetedByThisBoundary" in fleet
    assert "fleetContradictionsCannotBeRelabelledAsFormalGaps" in fleet
    assert "fleetExternalCountDoesNotCreateFormalDischarge" in fleet


def test_legal_authority_firewalls_are_directly_reachable() -> None:
    validation = read("DASHI/Unified/GovernedLegalFleetIbrahimTOEValidation.agda")

    required = (
        "rootCandidateSourceStillNotAuthority",
        "rootSameSystemStillNotAuthority",
        "rootValidityStillNotApplicability",
        "rootSemanticAdmissionStillNotLegalAuthority",
        "rootDocumentRoleStillNotLegalAuthority",
    )
    for symbol in required:
        assert symbol in validation


def test_ibrahim_pareto_and_snowball_firewalls_are_directly_reachable() -> None:
    validation = read("DASHI/Unified/GovernedLegalFleetIbrahimTOEValidation.agda")

    required = (
        "rootRecognitionParetoIsCanonical",
        "rootCharacterExecutionIsCanonical",
        "rootPhaseResolutionIsCanonical",
        "rootHistoricalDiscriminatorIsCanonical",
        "rootSearchPriorityStillNotProof",
        "rootProducerSourceStillNotExecution",
    )
    for symbol in required:
        assert symbol in validation


def test_changed_agda_surfaces_have_no_trust_escape_declarations() -> None:
    paths = (
        "DASHI/Unified/GovernedLegalWorkflowTOEBridgeExact.agda",
        "DASHI/Unified/GovernedLegalWorkflowTOEBridgeRegression.agda",
        "DASHI/Unified/BalabanIbrahimParetoSnowballTOEExact.agda",
        "DASHI/Unified/BalabanIbrahimParetoSnowballTOEValidation.agda",
        "DASHI/Unified/FleetFormalGapTargetTOEExact.agda",
        "DASHI/Unified/GovernedLegalFleetIbrahimTOEValidation.agda",
        "DASHI/EverythingTOESymmetryResolved369.agda",
        "DASHI/Unifier.agda",
        "DASHI/Unified/Everything.agda",
    )
    forbidden = (
        "postulate",
        "allow-unsolved-metas",
        "{-# TERMINATING #-}",
        "{-# NON_TERMINATING #-}",
        "NO_POSITIVITY_CHECK",
    )
    for path in paths:
        text = read(path)
        for token in forbidden:
            assert token not in text, (path, token)
