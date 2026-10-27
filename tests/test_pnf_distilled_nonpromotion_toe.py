from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

BRIDGE = ROOT / "DASHI/Unified/PNFDistilledNonPromotionTOEExact.agda"
VALIDATION = ROOT / "DASHI/Unified/PNFDistilledNonPromotionTOEValidation.agda"
UNIFIED = ROOT / "DASHI/Unified/Everything.agda"
TOE = ROOT / "DASHI/EverythingTOESymmetryResolved369.agda"
UNIFIER = ROOT / "DASHI/Unifier.agda"
WORKFLOW = ROOT / ".github/workflows/toe-symmetry-resolved-369.yml"


def read(path: Path) -> str:
    assert path.is_file(), f"missing {path.relative_to(ROOT)}"
    return path.read_text(encoding="utf-8", errors="strict")


def test_bridge_reuses_capsule_owners_without_duplicate_carriers():
    text = read(BRIDGE)
    for token in (
        "GluingOperatorLinearityProxyHarnessResult",
        "YMFiniteSelfAdjointHamiltonianProxyHarnessResult",
        "YMHamiltonianDominationProxyHarnessResult",
        "KluverFormConstantPsychedelicBoundaryExact",
        "FungalNetworkAgencyBoundary",
        "PsychogeographyYijingSourceAtlas",
        "DistributedEpistemicFabricSourceAtlasExact",
    ):
        assert token in text


def test_bridge_preserves_exact_nonpromotion_facts():
    text = read(BRIDGE)
    for token in (
        "Gluing.promotion_is_false",
        "Gluing.terminalPromotionIsFalse",
        "SelfAdjoint.promotion_is_false",
        "SelfAdjoint.terminalPromotionIsFalse",
        "Domination.promotion_is_false",
        "Domination.terminalPromotionIsFalse",
        "Kluver.formConstantDoesNotPromoteUniversalSymbol",
        "Kluver.formConstantDoesNotPromoteRecoveredMemory",
        "forestWideWoodWebClaimsNeedSpeciesSpecificEvidence",
        "myceliumNotInternetOrBrainByDefinition",
        "Psychogeography.webPublicationIdentifier",
        "Fabric.attributionRule",
    ):
        assert token in text


def test_zkp_receipt_is_fail_closed():
    text = read(BRIDGE)
    for token in (
        "PNFDistilledReuseZKPReceipt",
        "sharedLexemeCreatesSemanticIdentityIsFalse",
        "diagnosticCheckCreatesTheoremPromotionIsFalse",
        "sourceIdentifierCreatesProofAuthorityIsFalse",
        "esdSurfaceMutationAllowedIsFalse",
    ):
        assert token in text


def test_toe_surfaces_use_same_canonical_boundary():
    unified = read(UNIFIED)
    toe = read(TOE)
    unifier = read(UNIFIER)
    for text in (unified, toe, unifier):
        assert "PNFDistilledNonPromotionTOEExact" in text
        assert "canonicalPNFDistilledNonPromotionBoundary" in text
    assert "PNFDistilledNonPromotionTOEValidation" in unified
    assert "PNFDistilledNonPromotionTOEValidation" in toe


def test_validation_binds_unifier_to_canonical_objects():
    text = read(VALIDATION)
    for token in (
        "unifierUsesCanonicalPNFDistilledBoundary",
        "unifierUsesCanonicalPNFDistilledZKPReceipt",
        "gluingDiagnosticRemainsNonPromoting",
        "selfAdjointDiagnosticRemainsNonPromoting",
        "dominationDiagnosticRemainsNonPromoting",
        "fungalEvidenceRequirementRemainsTrue",
        "sharedLexemeDoesNotCreateSemanticIdentity",
        "diagnosticCheckDoesNotCreateTheoremPromotion",
        "sourceIdentifierDoesNotCreateProofAuthority",
        "esdMutationRemainsForbidden",
    ):
        assert token in text


def test_agda_surfaces_have_no_trust_escape():
    forbidden = (
        "postulate",
        "allow-unsolved-metas",
        "TERMINATING",
        "NO_POSITIVITY_CHECK",
        "{!!}",
    )
    for path in (BRIDGE, VALIDATION, TOE):
        text = read(path)
        for token in forbidden:
            assert token not in text, f"{token} found in {path.relative_to(ROOT)}"


def test_focused_workflow_covers_pnf_lane():
    text = read(WORKFLOW)
    for token in (
        "PNFDistilledNonPromotionTOEExact.agda",
        "PNFDistilledNonPromotionTOEValidation.agda",
        "test_pnf_distilled_nonpromotion_toe.py",
        "canonicalPNFDistilledNonPromotionBoundary",
        "dashi-agda-preflight",
        "ESD surface changed",
    ):
        assert token in text
