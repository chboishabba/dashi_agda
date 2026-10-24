"""Static/source-bound regression for the Aquino/Maxwell/Epstein/CA case delta.

These checks do NOT certify Agda, the source documents, or historical truth.
The Agda kernel command is tracked separately in the roadmap.
"""
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OWNER = ROOT / "DASHI/Cognition/AquinoMaxwellEpsteinCAMaxCutExact.agda"
ROLLUP = ROOT / "DASHI/Cognition/Everything.agda"
ROADMAP = ROOT / "docs/research/aquino-maxwell-epstein-ca-maxcut-20261024.md"


def test_existing_prior_art_reused_not_cloned():
    text = OWNER.read_text()
    assert "import DASHI.Cognition.BannonCambridgeAnalyticaInfluenceInfrastructureExact as CA" in text
    assert "import DASHI.Cognition.EpsteinMasterPlanAttributionBoundaryExact as Plan" in text
    assert "import DASHI.Governance.EvidenceGradedGenealogyCore as Genealogy" in text
    assert "module DASHI.Cognition.AquinoMaxwellEpsteinCAMaxCutExact where" in text
    assert "import DASHI.Cognition.AquinoMaxwellEpsteinCAMaxCutExact" in ROLLUP.read_text()


def test_source_roots_roles_and_contradictions_are_retained():
    text = OWNER.read_text()
    for fragment in (
        "wylieRoot", "aquinoVallelyRoot", "fourthCircuitRoot",
        "ftcRoot", "houseJudiciaryRoot", "buaDOJRoot",
        "dojFBIMemoRoot", "epsteinCorrespondenceRoot",
        "judicialProceduralDecision", "regulatoryFinding",
        "attributedFirstPersonTestimony", "disputedAgencyReview",
        "1992-02-26", "2025-07",
    ):
        assert fragment in text
    assert "The House hearing and Wylie's submitted statement" in ROADMAP.read_text()


def test_attribution_firewalls_and_same_object_checks():
    text = OWNER.read_text()
    for fragment in (
        "robertMaxwellIsNotRobertMercer ()",
        "mindWarIsNotStargate ()",
        "aquinoToSCLUnpaid = refl",
        "aquinoToEpsteinUnpaid = refl",
        "promisMaxwellUnpaid = refl",
        "unifiedHierarchyUnpaid = refl",
        "existingCAMediaReuseUnpaid = refl",
        "existingMasterPlanHierarchyUnpaid = refl",
        "existingGenealogyDoesNotPromoteAnalogy = refl",
        "noWitnessMultiplication ()",
        "noTechniquePromotion ()",
        "noGuiltByAllegation ()",
        "noUnifiedCommandFromNetworkPath ()",
    ):
        assert fragment in text


def test_source_locator_or_attributed_local_owner():
    text = OWNER.read_text()
    assert "https://committees.parliament.uk/writtenevidence/89475/html/" in text
    assert "https://law.justia.com/cases/federal/appellate-courts/F2/957/139/2044/" in text
    assert "https://www.justice.gov/opa/media/1407001/dl" in text
    assert "TrumpMarALagoBannonBridgeExact" in text
    assert ROADMAP.exists()


def test_shared_provenance_and_woogaroo_method_preserved_as_secondary():
    source = OWNER.read_text()
    owners = {
        "DASHI.Law.EvidenceProvenanceDependencyDagExact as Provenance":
            ROOT / "DASHI/Law/EvidenceProvenanceDependencyDagExact.agda",
        "DASHI.Core.ProvenanceClosureIndependenceExact as RootClosure":
            ROOT / "DASHI/Core/ProvenanceClosureIndependenceExact.agda",
        "DASHI.Core.SourceAcquisitionGeometryExact as Acquisition":
            ROOT / "DASHI/Core/SourceAcquisitionGeometryExact.agda",
        "DASHI.Core.MultipartSameObjectReconstructionExact as Multipart":
            ROOT / "DASHI/Core/MultipartSameObjectReconstructionExact.agda",
    }
    for module, path in owners.items():
        assert f"import {module}" in source
        assert path.exists(), f"Missing existing canonical owner: {path}"
    # Case-specific evidence is NOT imported from a separate unrelated legal fact.
    assert "import DASHI.Law.SensibLawWoogarooEvidenceDependencyMatrixExact" not in source


def test_bidi_source_independence_and_acquisition_stages():
    source = OWNER.read_text()
    for fragment in (
        "caseIndependentProducerRequirement = refl",
        "Provenance.reverseProvenance Provenance.independentCorroborationConsumer",
        "Provenance.independentProducerReceipt",
        "caseReprintsNotIndependent = refl",
        "caseSearchAbsenceNotHistoricalAbsence = refl",
        "caseIdentityNeedsFullReconstruction = refl",
        "discoveryDoesNotPayInspection ()",
        "proceduralFindingDoesNotPaySubstantiveFact ()",
        "eventTimeOverlapDoesNotPayCommand ()",
        "analogyDoesNotPayProgramme ()",
    ):
        assert fragment in source


def test_per_consumer_witnesses_remain_unpaid_without_original_artefacts():
    source = OWNER.read_text()
    for named_cut in (
        "cambridgeLegalEntityCut", "sclTransferCut", "bannonWorkProductCut",
        "promisExecutableCut", "aquinoHistoricalTransferCut",
        "commandHierarchyCut",
    ):
        assert f"{named_cut} : CaseDependencyCut" in source
        assert f"{named_cut} = case-dependency-cut" in source
    assert source.count("true true true false false") >= 6
    assert "canonicalCaseCuts : List CaseDependencyCut" in source
    for target in (
        "sclCorporateWorkProductTarget", "bannonEpsteinFilmWorkProductTarget",
        "promisMaxwellExecutableTarget", "aquinoSCLTransferTarget",
    ):
        assert f"{target} = Acquisition.sourceAcquisitionTarget" in source
    assert source.count("false false false") >= 4


def test_missing_scientists_is_primary_programme_investigation_index():
    source = OWNER.read_text()
    owners = (
        "DASHI.Culture.MissingDeceasedCommonObjectProgrammeDiscriminatorExact as Common",
        "DASHI.Culture.MissingDeceasedCommonProgrammePromotionParetoExact as ProgrammeFrontier",
        "DASHI.Culture.MissingDeceasedTwentyScientistRound48AntiEchoChamberMethodologyExact as AntiEcho",
        "DASHI.Core.EventTimeCapabilityAlignmentBidiExact as EventTime",
        "DASHI.Core.CapabilityFragilityConfoundersBidiExact as Fragility",
        "DASHI.Culture.MissingDeceasedCustodyEventTimeMatrixExact as Custody",
        "DASHI.Cognition.TrumpMarALagoBannonBridgeExact as BannonBridge",
    )
    for owner in owners:
        assert f"import {owner}" in source
    assert "import DASHI.Core.ITIRInvestigationAcquisitionParetoExact" not in source
    assert "import DASHI.Core.ITIRInvestigationWorkbenchProjectionExact" not in source


def test_scope_indexed_h0_to_h3_nonpromotion():
    source = OWNER.read_text()
    for token in (
        "caseCommonObjectMethodDoesNotPayCoordination = refl",
        "caseTechnicalAdjacencyDoesNotPaySameObject = refl",
        "caseSourceRepetitionDoesNotPayIndependence = refl",
        "caseRequiresActualOperationalEvidence = refl",
        "BannonBridge.relationshipOrInstitutionalEdgePaid",
        "bannonEpsteinContactLocatedInOwner = refl",
        "bannonEpsteinToCommonProgrammeUnpaid = refl",
        "historicalCommonCommandCut = programme-hypothesis-cut",
        "proposedCrossGenerationalIntelligenceCommand Common.H1",
        "false false",
    ):
        assert token in source


def test_primary_programme_frontier_and_event_time_custody():
    source = OWNER.read_text()
    for token in (
        "bannonEpsteinWorkProductSearch = ProgrammeFrontier.promotion-search-candidate",
        "aquinoToSCLObjectSearch = ProgrammeFrontier.promotion-search-candidate",
        "maxwellPROMISNetworkSearch = ProgrammeFrontier.promotion-search-candidate",
        "caseProgrammeSearchFront : List ProgrammeFrontier.PromotionSearchCandidate",
        "aquinoLaterSCLControl = EventTime.event-time-capability-receipt",
        "bannonCAMethodLaterUse = EventTime.event-time-capability-receipt",
        "EventTime.unresolvedTime",
        "eventTimeNonPromotion = refl",
        "sclIPLicensingAlternative = Fragility.fragility-receipt",
        "mundaneExplanationsFirst = refl",
        "custodyNonPromotion = refl",
    ):
        assert token in source


def test_anti_echo_chamber_disconfirming_search_is_explicitly_unfinished():
    source = OWNER.read_text()
    for token in (
        "caseAdversarialSearch = AntiEcho.claim-search-boundary",
        "caseHypothesisTest = AntiEcho.hypothesis-test-boundary",
        "AntiEcho.oneCommonProgramme",
        "false true false",
        "caseCounterEvidenceRequired = refl",
        "caseSearchAbsenceNotHistoricalAbsence = refl",
        "caseAntiPanopticon = refl",
        "caseNarrativeNotAuthority = refl",
    ):
        assert token in source


def test_constructive_shared_root_refutation_reuses_existing_proof():
    source = OWNER.read_text()
    assert "import DASHI.Core.AffectedDependencyClosureExact as Affected" in source
    for token in (
        "data ReprintCarrier : Set where",
        "statementToExcerptA : ReprintDependency firstPersonStatement excerptA",
        "statementToExcerptB : ReprintDependency firstPersonStatement excerptB",
        "reprintSystem = RootClosure.provenanceSystem ReprintDependency ReprintRoot",
        "twoExcerptsShareOneRoot = RootClosure.sharedUpstreamRoot",
        "(Affected.affectedStep statementToExcerptA Affected.affectedRefl)",
        "(Affected.affectedStep statementToExcerptB Affected.affectedRefl)",
        "sharedReprintRootRefutesIndependence =",
        "RootClosure.sharedUpstreamRootRefutesIndependence twoExcerptsShareOneRoot",
    ):
        assert token in source


def test_four_competing_hypotheses_have_explicit_counter_searches():
    source = OWNER.read_text()
    for name in (
        "caseIndependentNetworksTest", "caseLocalSubclustersTest",
        "caseOneCrossGenerationalProgrammeTest", "caseOperationalDirectionTest",
    ):
        assert f"{name} = AntiEcho.hypothesis-test-boundary" in source
    for clazz in (
        "AntiEcho.distributedIndependentProgrammes",
        "AntiEcho.linkedSubclusters",
        "AntiEcho.oneCommonProgramme",
        "AntiEcho.coordinatedTargeting",
    ):
        assert clazz in source
    assert "caseCompetingHypotheses : List AntiEcho.HypothesisTestBoundary" in source
    assert "caseWholeH2Unpaid = refl" in source
    assert "caseCovertH3Unpaid = refl" in source
    assert "NOT scientist targeting" in source
    assert "Robert Maxwell/Robert Mercer" in source
