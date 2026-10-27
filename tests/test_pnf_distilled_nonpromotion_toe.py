from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

SOURCE = ROOT / "DASHI/Unified/PNFSourceBoundaryTOEExact.agda"
SOURCE_VALIDATION = ROOT / "DASHI/Unified/PNFSourceBoundaryTOEValidation.agda"
DISTILLED = ROOT / "DASHI/Unified/PNFDistilledNonPromotionTOEExact.agda"
DISTILLED_VALIDATION = ROOT / "DASHI/Unified/PNFDistilledNonPromotionTOEValidation.agda"
UNIFIED = ROOT / "DASHI/Unified/Everything.agda"
TOE = ROOT / "DASHI/EverythingTOESymmetryResolved369.agda"
UNIFIER = ROOT / "DASHI/Unifier.agda"
WORKFLOW = ROOT / ".github/workflows/toe-symmetry-resolved-369.yml"


def read(path: Path) -> str:
    assert path.is_file(), f"missing {path.relative_to(ROOT)}"
    return path.read_text(encoding="utf-8", errors="strict")


def test_canonical_source_boundary_reuses_capsule_owners():
    text = read(SOURCE)
    for token in (
        "GluingOperatorLinearityProxyHarnessResult",
        "YMFiniteSelfAdjointHamiltonianProxyHarnessResult",
        "YMHamiltonianDominationProxyHarnessResult",
        "KluverFormConstantPsychedelicBoundaryExact",
        "FungalNetworkAgencyBoundary",
        "PsychogeographyYijingSourceAtlas",
        "ITIRRelationalInterlinguaConsumerFibreExact",
        "IbrahimSnowballEvidenceSynthesisSourceIndependenceParetoBidiExact",
        "IbrahimSnowballInformationCascadeEvidenceDependencyHyperfabricBidiExact",
    ):
        assert token in text


def test_canonical_source_boundary_preserves_exact_facts():
    text = read(SOURCE)
    for token in (
        "canonicalGluingHarnessDoesNotProveTrueLinearity",
        "canonicalHarnessFiniteSelfAdjointTheoremFalse",
        "canonicalHamiltonianDominationProxyTheoremFalse",
        "forestWideWoodWebClaimsNeedSpeciesSpecificEvidence",
        "myceliumNotInternetOrBrainByDefinition",
        "formConstantDoesNotPromoteUniversalSymbol",
        "formConstantDoesNotPromoteRecoveredMemory",
        "webPublicationIdentifier",
        "canonicalPNFSourceBoundaryTOEReceipt",
        "wordsDoNotPayPredicate",
        "pnfCandidateNotTruth",
        "perceivedIndependenceDoesNotCreateActualIndependence",
        "repetitionDoesNotMeanIndependentEvidence",
        "commonSourceDoesNotMeanNoEvidence",
    ):
        assert token in text


def test_distilled_facade_reuses_canonical_source_boundary_only():
    text = read(DISTILLED)
    assert "import DASHI.Unified.PNFSourceBoundaryTOEExact as Boundary" in text
    assert "DistributedEpistemicFabricSourceAtlasExact" in text
    assert "canonicalPNFSourceBoundaryTOEReceipt" in text

    # The compatibility facade must not recreate the donor theorem package.
    for token in (
        "import DASHI.Physics.Closure.GluingOperatorLinearityProxyHarnessResult",
        "import DASHI.Physics.Closure.YMFiniteSelfAdjointHamiltonianProxyHarnessResult",
        "import DASHI.Physics.Closure.YMHamiltonianDominationProxyHarnessResult",
        "import DASHI.Biology.KluverFormConstantPsychedelicBoundaryExact",
        "import DASHI.Biology.Levin.FungalNetworkAgencyBoundary",
        "import DASHI.Biology.PsychogeographyYijingSourceAtlas",
    ):
        assert token not in text


def test_zkp_receipt_is_fail_closed():
    text = read(DISTILLED)
    for token in (
        "PNFDistilledReuseZKPReceipt",
        "sharedLexemeCreatesSemanticIdentityIsFalse",
        "diagnosticCheckCreatesTheoremPromotionIsFalse",
        "sourceIdentifierCreatesProofAuthorityIsFalse",
        "esdSurfaceMutationAllowedIsFalse",
        "Fabric.attributionRule",
    ):
        assert token in text


def test_all_three_toe_facades_use_canonical_source_boundary():
    unified = read(UNIFIED)
    toe = read(TOE)
    unifier = read(UNIFIER)

    for text in (unified, toe, unifier):
        assert "PNFSourceBoundaryTOEExact" in text
        assert "canonicalPNFSourceBoundaryTOEReceipt" in text

    assert "toePNFSourceBoundaryReceipt" in toe
    assert "toePNFSourceBoundaryReceipt" in unifier
    assert "pnfSourceBoundaryReceipt" in unified


def test_source_validation_binds_unifier_to_canonical_source_owner():
    text = read(SOURCE_VALIDATION)
    for token in (
        "unifierUsesCanonicalPNFSourceBoundaryReceipt",
        "gluingFacadeExact",
        "selfAdjointFacadeExact",
        "dominationFacadeExact",
        "fungalFacadeExact",
        "kluverCobwebFacadeExact",
        "webIdentifierFacadeExact",
        "identicalWordsFirewallFacadeExact",
        "commonFingerprintFirewallFacadeExact",
        "perceivedIndependenceFirewallFacadeExact",
        "repetitionFirewallFacadeExact",
        "commonSourceFirewallFacadeExact",
    ):
        assert token in text


def test_distilled_validation_only_checks_process_firewalls():
    text = read(DISTILLED_VALIDATION)
    assert "import DASHI.Unified.PNFSourceBoundaryTOEValidation" in text
    for token in (
        "unifierUsesCanonicalPNFDistilledZKPReceipt",
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
    for path in (
        SOURCE,
        SOURCE_VALIDATION,
        DISTILLED,
        DISTILLED_VALIDATION,
        TOE,
    ):
        text = read(path)
        for token in forbidden:
            assert token not in text, f"{token} found in {path.relative_to(ROOT)}"


def test_focused_workflow_covers_canonical_and_compatibility_lanes():
    text = read(WORKFLOW)
    for token in (
        "PNFSourceBoundaryTOEExact.agda",
        "PNFSourceBoundaryTOEValidation.agda",
        "PNFDistilledNonPromotionTOEExact.agda",
        "PNFDistilledNonPromotionTOEValidation.agda",
        "test_pnf_distilled_nonpromotion_toe.py",
        "canonicalPNFSourceBoundaryTOEReceipt",
        "canonicalPNFDistilledReuseZKPReceipt",
        "dashi-agda-preflight",
        "ESD surface change detected",
    ):
        assert token in text


def test_unified_aggregate_inherited_compile_blockers_are_repaired():
    text = read(UNIFIED)
    assert "navierStokesRemainsNonPromoting =\n  Physics.navierStokesJPromotionBlocked" in text
    assert "yangMillsRemainsNonPromoting =\n  Physics.yangMillsJPromotionBlocked" in text
    assert "navierStokesFormalProjectionsRemainNonPromoting :\n  ∀ kind →" in text
    assert "yangMillsFormalProjectionsRemainNonPromoting :\n  ∀ kind →" in text
    assert "import DASHI.Physics.Foundations.Round5FullBoundary as Round5" not in text
