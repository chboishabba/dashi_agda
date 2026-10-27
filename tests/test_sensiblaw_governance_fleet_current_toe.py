from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OWNER = ROOT / "DASHI/Unified/SensibLawGovernanceFleetTOEExact.agda"
TOE = ROOT / "DASHI/EverythingTOESymmetryResolved369.agda"
UNIFIER = ROOT / "DASHI/Unifier.agda"
UNIFIED = ROOT / "DASHI/Unified/Everything.agda"
WORKFLOW = ROOT / ".github/workflows/toe-symmetry-resolved-369.yml"

def read(path: Path) -> str:
    assert path.is_file(), f"missing {path.relative_to(ROOT)}"
    return path.read_text(encoding="utf-8", errors="strict")

def test_owner_reuses_canonical_governance_and_fleet_donors():
    text = read(OWNER)
    for token in (
        "SensibLawSemanticPromotionPolicy as Semantic",
        "SensibLawLegalSourceAuthorityEvidenceExact as LegalAuthority",
        "SensibLawAgdaFirstLegalRuntimeEverything as LegalRuntime",
        "DomainPermeabilityAuthorityTransport as Domain",
        "SnowballAttributionProvenanceInvariantExact as Snowball",
        "SensibLawSnowballAttributionLineageAdapterExact as SnowballLineage",
        "SensibLawParetoProofDirectedCorpusSearchEverything as ParetoSearch",
        "SensibLawNativeLegalFollowCLIExact as NativeFollow",
        "SensibLawPreferredAustralianAuthorityAcquisitionExact as Acquisition",
        "SensibLawExpertEvidenceProductionIntegrityExact as Expert",
        "FleetFormalGapTargetTOEExact as Fleet",
    ):
        assert token in text

def test_owner_carries_fail_closed_boundaries():
    text = read(OWNER)
    for token in (
        "governanceSemanticAllAuthorityStillClosed",
        "governanceCandidateSourceDoesNotCloseAuthority",
        "governanceSameSystemDoesNotCloseAuthority",
        "governanceCurrentValidityDoesNotEstablishApplicability",
        "governanceDocumentRoleDoesNotCreateLegalAuthority",
        "governanceRuntimeCannotInventLegalSemantics",
        "governanceSourceFollowCannotBecomeAuthorityByTransport",
        "governanceSameMachineryDoesNotTransportAuthority",
        "governanceSnowballCitationDoesNotCreateAuthority",
        "governanceParetoDirectiveIsNotLegalAuthority",
        "governanceNativeCliDoesNotCreateLegalAuthority",
        "governanceProviderFailureDoesNotMakePropositionFalse",
        "governanceExpertProductionPromotesNoAuthority",
    ):
        assert token in text

def test_owner_targets_only_formal_gap_frontier():
    text = read(OWNER)
    for token in (
        "governanceFleetDischargedFibresAre584",
        "governanceFleetContradictionGapsAre44",
        "governanceFleetFormalGapsAre58",
        "governanceFleetMacroscopicMotifsAre3",
        "governanceFleetTargetsOnlyUnformalisedFormalGaps",
        "governanceFleetDischargedFibresRemainDischarged",
        "governanceFleetContradictionsRemainSeparate",
        "governanceFleetSpectralLabelsDoNotIdentifyTheoremOwners",
    ):
        assert token in text

def test_all_three_toe_facades_expose_same_owner():
    root = read(TOE)
    unifier = read(UNIFIER)
    unified = read(UNIFIED)
    assert "SensibLawGovernanceFleetTOEExact as GovernanceFleet" in root
    assert "toeSensibLawGovernanceFleetReceipt" in root
    assert "SensibLawGovernanceFleetTOEExact as GovernanceFleet" in unifier
    assert "unifierSensibLawGovernanceFleetReceipt" in unifier
    assert "SensibLawGovernanceFleetTOEExact as GovernanceFleet" in unified
    assert "unifiedSensibLawGovernanceFleetReceipt" in unified

def test_zero_trust_escape_and_esd_mutation_in_owner():
    text = read(OWNER)
    for token in ("postulate", "allow-unsolved-metas", "TERMINATING", "NO_POSITIVITY_CHECK", "{!!}"):
        assert token not in text
    assert "dashi_digital_esd" not in text
    assert "digital_esd" not in text

def test_workflow_has_referee_and_preflight_for_current_owner():
    text = read(WORKFLOW)
    for token in (
        "SensibLawGovernanceFleetTOEExact.agda",
        "canonicalSensibLawGovernanceFleetTOEReceipt",
        "dashi-repo related",
        "dashi-repo discover",
        "dashi-repo lineage",
        "dashi-agda-preflight",
        "ESD surface change detected",
    ):
        assert token in text
