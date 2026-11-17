from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

HANDOFF = ROOT / "DASHI/Unified/GovernedLegalWorkflowSourceSemanticTOEExact.agda"
REGRESSION = ROOT / "DASHI/Unified/GovernedLegalWorkflowSourceSemanticTOERegression.agda"
TOE = ROOT / "DASHI/EverythingTOESymmetryResolved369.agda"
UNIFIER = ROOT / "DASHI/Unifier.agda"
UNIFIED = ROOT / "DASHI/Unified/Everything.agda"
WORKFLOW = ROOT / ".github/workflows/toe-symmetry-resolved-369.yml"


def read(path: Path) -> str:
    assert path.is_file(), f"missing {path.relative_to(ROOT)}"
    return path.read_text(encoding="utf-8", errors="strict")


def test_handoff_reuses_only_normalized_owners():
    text = read(HANDOFF)
    assert "GovernedLegalWorkflowSourceGenealogyTOEExact as LegalSource" in text
    assert "PNFDistilledNonPromotionTOEExact as Distilled" in text
    assert "IbrahimSnowball" not in text
    assert "Actionstep" not in text


def test_handoff_contains_only_existing_nonpromotion_coordinates():
    text = read(HANDOFF)
    for token in (
        "legalSourceGenealogyHandoff",
        "distilledNonPromotionReceipt",
        "sharedLexemeCreatesSemanticIdentityIsFalse",
        "diagnosticCheckCreatesTheoremPromotionIsFalse",
        "sourceIdentifierCreatesProofAuthorityIsFalse",
        "esdSurfaceMutationAllowedIsFalse",
        "legalRuntimeContract",
        "runtimeInventsLegalSemanticsIsFalse",
        "sourceFollowCreatesAuthorityIsFalse",
        "domainTransportReceipt",
        "targetDomainNeedsOwnAuthorityWitnessIsTrue",
        "representationEqualityCreatesLegalAuthorityIsFalse",
        "vendorIdentityCreatesAuthorityIsFalse",
        "canonicalGovernedLegalWorkflowSourceSemanticHandoff",
    ):
        assert token in text


def test_all_toe_facades_reach_same_handoff():
    root = read(TOE)
    unifier = read(UNIFIER)
    unified = read(UNIFIED)
    assert "toeGovernedLegalWorkflowSourceSemanticHandoff" in root
    assert "unifierGovernedLegalWorkflowSourceSemanticHandoff" in unifier
    assert "governedLegalWorkflowSourceSemanticHandoff" in unified
    for text in (root, unifier, unified):
        assert "GovernedLegalWorkflowSourceSemanticTOEExact as LegalSourceSemantic" in text
    for token in (
        "toeGovernedRuntimeCannotInventLegalSemantics",
        "toeGovernedSourceFollowCannotCreateAuthorityByTransport",
        "toeGovernedTargetDomainNeedsOwnAuthorityWitness",
        "toeGovernedRepresentationEqualityDoesNotCreateLegalAuthority",
        "toeGovernedVendorIdentityDoesNotCreateAuthority",
    ):
        assert token in root
    for token in (
        "unifierGovernedRuntimeCannotInventLegalSemantics",
        "unifierGovernedSourceFollowCannotCreateAuthorityByTransport",
        "unifierGovernedTargetDomainNeedsOwnAuthorityWitness",
        "unifierGovernedRepresentationEqualityDoesNotCreateLegalAuthority",
        "unifierGovernedVendorIdentityDoesNotCreateAuthority",
    ):
        assert token in unifier
    for token in (
        "governedRuntimeCannotInventLegalSemantics",
        "governedSourceFollowCannotCreateAuthorityByTransport",
        "governedTargetDomainNeedsOwnAuthorityWitness",
        "governedRepresentationEqualityDoesNotCreateLegalAuthority",
        "governedVendorIdentityDoesNotCreateAuthority",
    ):
        assert token in unified


def test_regression_binds_unifier_to_canonical_handoff():
    text = read(REGRESSION)
    for token in (
        "legalSourceHandoffIsCanonical",
        "distilledReceiptIsCanonical",
        "sharedLexemeStillDoesNotCreateSemanticIdentity",
        "diagnosticCheckStillDoesNotCreateTheoremPromotion",
        "sourceIdentifierStillDoesNotCreateProofAuthority",
        "esdMutationStillForbidden",
        "runtimeContractIsCanonical",
        "domainTransportReceiptIsCanonical",
        "runtimeSemanticsStillFailClosed",
        "sourceFollowAuthorityStillFailClosed",
        "representationAuthorityStillFailClosed",
        "vendorAuthorityStillFailClosed",
        "targetDomainAuthorityWitnessStillRequired",
        "unifierHandoffIsCanonical",
    ):
        assert token in text


def test_zero_trust_escape_in_new_agda_lane():
    forbidden = (
        "postulate",
        "allow-unsolved-metas",
        "TERMINATING",
        "NO_POSITIVITY_CHECK",
        "{!!}",
    )
    for path in (HANDOFF, REGRESSION):
        text = read(path)
        for token in forbidden:
            assert token not in text, f"{token} found in {path.relative_to(ROOT)}"


def test_workflow_covers_referee_preflight_esd_and_kernel():
    text = read(WORKFLOW)
    for token in (
        "GovernedLegalWorkflowSourceSemanticTOEExact.agda",
        "GovernedLegalWorkflowSourceSemanticTOERegression.agda",
        "canonicalGovernedLegalWorkflowSourceSemanticHandoff",
        "dashi-repo related",
        "dashi-repo discover",
        "dashi-repo lineage",
        "dashi-agda-preflight",
        "ESD surface change detected",
    ):
        assert token in text
