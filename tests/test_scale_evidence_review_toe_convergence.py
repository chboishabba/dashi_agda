from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

BRIDGE = ROOT / "DASHI/Unified/SCALEEvidenceReviewTOEConvergenceExact.agda"
VALIDATION = ROOT / "DASHI/Unified/SCALEEvidenceReviewTOEConvergenceValidation.agda"
TOE = ROOT / "DASHI/EverythingTOESymmetryResolved369.agda"
UNIFIER = ROOT / "DASHI/Unifier.agda"
UNIFIED = ROOT / "DASHI/Unified/Everything.agda"
WORKFLOW = ROOT / ".github/workflows/toe-symmetry-resolved-369.yml"


def read(path: Path) -> str:
    assert path.is_file(), f"missing {path.relative_to(ROOT)}"
    return path.read_text(encoding="utf-8", errors="strict")


def test_bridge_reuses_existing_scale_review_owners():
    text = read(BRIDGE)
    for token in (
        "SensibLawScale1ExactReplayEconomyReceipt",
        "SensibLawProductionScaleAcceptanceExact",
        "SensibLawReviewProjectionEconomyExact",
        "SensibLawDbNativeCommitEconomyExact",
        "ITIRRelationalInterlinguaConsumerFibreExact",
        "RuntimeWitnessFormalRefinementExact",
        "ITIRGovernanceControlCaseExact",
        "ITIRInvestigationAcquisitionParetoExact",
        "ITIRInvestigationWorkbenchProjectionExact",
        "SLRReviewedEvidencePaymentExact",
        "MaboReviewedEvidencePaymentExact",
        "PNFSourceBoundaryTOEExact",
        "SLRLegalRuntimeCapstoneExact",
        "GovernedLegalWorkflowTOEBridgeExact",
    ):
        assert token in text


def test_bridge_exposes_exact_nonpromotion_firewalls():
    text = read(BRIDGE)
    for token in (
        "scaleReplayDoesNotPromoteSemanticTruth",
        "productionScaleDoesNotCreateSemanticAuthority",
        "reviewProjectionReuseDoesNotCreateClaimTruth",
        "commitCoalescingDoesNotCreateSemanticAuthority",
        "fewCommitBarriersDoNotProveSemanticIndependence",
        "commonPnfFingerprintDoesNotCreateClaimTruth",
        "reviewedEvidenceDoesNotCreateClaimTruth",
        "reviewedEvidenceDoesNotCreateSemanticAuthority",
        "maboReviewedPaymentDoesNotEqualClaimTruth",
        "perceivedIndependenceDoesNotCreateProvenanceIndependence",
        "repetitionDoesNotCreateIndependentEvidence",
        "commonSourceDoesNotEraseEvidence",
        "passingControlDoesNotMeanCertified",
        "frontierRouteDoesNotGrantAuthorization",
        "uiCannotGeneratePresentSource",
        "potentialReopeningDoesNotBecomeActual",
    ):
        assert token in text


def test_runtime_witness_remains_proof_relevant():
    text = read(BRIDGE)
    assert "runtimeWitnessRefinementRequiresPremise" in text
    assert "RuntimeWitness.RefinedWitness Premise" in text
    assert "runtimeWitnessCanForgetFormalPremise" in text


def test_zkp_frame_is_explicit_and_non_esd():
    text = read(BRIDGE)
    for token in (
        "O. Objective.",
        "R. Reuse.",
        "C. Construction.",
        "S. Safety.",
        "L. Lane.",
        "P. Preconditions.",
        "P. Invariants.",
        "P. Postconditions.",
        "SCALEEvidenceReviewTOEZKPFrame",
        "canonicalSCALEEvidenceReviewTOEZKPFrame",
        "G. Governance.",
        "F. Verification.",
        "It edits no ESD or digital_esd surface.",
    ):
        assert token in text


def test_validation_reopens_canonical_owners():
    text = read(VALIDATION)
    for token in (
        "receiptUsesCanonicalReplay",
        "receiptUsesCanonicalReviewProjectionEconomy",
        "receiptUsesCanonicalGovernance",
        "receiptUsesCanonicalInvestigation",
        "receiptUsesCanonicalWorkbench",
        "receiptUsesCanonicalReviewedEvidence",
        "receiptUsesCanonicalMaboReview",
        "receiptUsesCanonicalPNFSourceBoundary",
        "receiptUsesCanonicalLegalRuntime",
        "receiptUsesCanonicalLegalWorkflow",
    ):
        assert token in text


def test_attached_to_all_three_toe_surfaces():
    toe = read(TOE)
    unifier = read(UNIFIER)
    unified = read(UNIFIED)
    assert "SCALEEvidenceReviewTOEConvergenceExact as SCALEReview" in toe
    assert "toe369SCALEEvidenceReviewTOEReceipt" in toe
    assert "toe369SCALEEvidenceReviewTOEZKPFrame" in toe
    assert "toe369SCALEReviewDoesNotCreateClaimTruth" in toe
    assert "toe369SCALEReviewProjectionReuseDoesNotCreateClaimTruth" in toe
    assert "toe369SCALECommitCoalescingDoesNotCreateSemanticAuthority" in toe
    assert "toe369SCALEPerceivedIndependenceDoesNotCreateProvenanceIndependence" in toe
    assert "toe369SCALERepetitionDoesNotCreateIndependentEvidence" in toe
    assert "SCALEEvidenceReviewTOEConvergenceExact as SCALEReview" in unifier
    assert "unifierSCALEEvidenceReviewTOEReceipt" in unifier
    assert "unifierSCALEEvidenceReviewTOEZKPFrame" in unifier
    assert "unifierSCALEFrontierDoesNotGrantAuthorization" in unifier
    assert "unifierSCALEReviewProjectionReuseDoesNotCreateClaimTruth" in unifier
    assert "unifierSCALECommitCoalescingDoesNotCreateSemanticAuthority" in unifier
    assert "unifierSCALEPerceivedIndependenceDoesNotCreateProvenanceIndependence" in unifier
    assert "unifierSCALERepetitionDoesNotCreateIndependentEvidence" in unifier
    assert "SCALEEvidenceReviewTOEConvergenceExact as SCALEReview" in unified
    assert "scaleEvidenceReviewTOEReceipt" in unified
    assert "scaleEvidenceReviewTOEZKPFrame" in unified
    assert "scaleEvidenceReviewReviewProjectionReuseDoesNotCreateClaimTruth" in unified
    assert "scaleEvidenceReviewCommitCoalescingDoesNotCreateSemanticAuthority" in unified
    assert "scaleEvidenceReviewPerceivedIndependenceDoesNotCreateProvenanceIndependence" in unified
    assert "scaleEvidenceReviewRepetitionDoesNotCreateIndependentEvidence" in unified


def test_bridge_adds_no_trust_escape():
    forbidden = ("postulate", "allow-unsolved-metas", "TERMINATING",
                 "NO_POSITIVITY_CHECK", "{!!}")
    for path in (BRIDGE, VALIDATION):
        text = read(path)
        for token in forbidden:
            assert token not in text


def test_workflow_has_referee_preflight_and_kernel_targets():
    text = read(WORKFLOW)
    for token in (
        "SCALEEvidenceReviewTOEConvergenceExact.agda",
        "SCALEEvidenceReviewTOEConvergenceValidation.agda",
        "canonicalSCALEEvidenceReviewTOEReceipt",
        "dashi-repo related",
        "dashi-repo discover",
        "dashi-repo lineage",
        "dashi-agda-preflight",
    ):
        assert token in text


def test_unified_facade_reuses_existing_physics_nonpromotion_owners():
    text = read(UNIFIED)
    assert "navierStokesRemainsNonPromoting =\n  Physics.navierStokesJPromotionBlocked" in text
    assert "yangMillsRemainsNonPromoting =\n  Physics.yangMillsJPromotionBlocked" in text
    assert "Spine.canonicalInvariantObjectsDoNotPromoteFormalProjections\n    Physics.navierStokesObject" in text
    assert "Spine.canonicalInvariantObjectsDoNotPromoteFormalProjections\n    Physics.yangMillsObject" in text
    assert "import DASHI.Physics.Foundations.Round5FullBoundary as Round5" not in text


def test_source_genealogy_reuses_normalized_pnf_source_boundary():
    text = read(BRIDGE)
    assert "import DASHI.Unified.PNFSourceBoundaryTOEExact as PNFSource" in text
    assert "IbrahimSnowballEvidenceSynthesisSourceIndependenceParetoBidiExact as IbrahimIndependence" not in text
    assert "IbrahimSnowballInformationCascadeEvidenceDependencyHyperfabricBidiExact as IbrahimDependency" not in text
    assert "PNFSource.commonPnfFingerprintDoesNotCreateClaimTruth" in text
    assert "PNFSource.perceivedIndependenceDoesNotCreateProvenanceIndependence" in text
    assert "PNFSource.repetitionDoesNotCreateIndependentEvidence" in text
    assert "PNFSource.commonSourceDoesNotEraseEvidence" in text
