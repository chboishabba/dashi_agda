"""Static/source-bound regression for the Aquino/Maxwell/Epstein/CA case delta.

These checks do NOT certify Agda, the source documents, or historical truth.
The Agda kernel command is tracked separately in the roadmap.
"""
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OWNER = ROOT / "DASHI/Cognition/AquinoMaxwellEpsteinCAMaxCutExact.agda"
ROLLUP = ROOT / "DASHI/Cognition/Everything.agda"
ROADMAP = ROOT / "docs/research/aquino-maxwell-epstein-ca-maxcut-20261024.md"
PRIOR_FILM_OWNER = ROOT / "DASHI/Cognition/TrumpMarALagoBannonBridgeExact.agda"


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
        "DASHI.Culture.MissingDeceasedTwentyScientistRound50ProfessionalEvidenceRoomExact as EvidenceRoom",
        "DASHI.Culture.MissingDeceasedTwentyScientistRound43NarrativeEvidenceStrataExact as Narrative",
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


def test_shared_native_evidence_item_not_promoted_to_source_truth():
    source = OWNER.read_text()
    for token in (
        "wylieEvidenceRoomItem = EvidenceRoom.shared-evidence-room-item",
        "UNCOMPUTED: no native bytes in case branch",
        "Christopher Wylie author root; Parliamentary publication is not a second eyewitness",
        "wylieInvestigatorGate = EvidenceRoom.investigator-gate",
        "true true false false",
        "unverifiedMasterPlanPublicationGate = EvidenceRoom.journalist-gate",
        "NOT READY: unsupported causal allegation",
        "investigationNotPublication = refl",
        "admissibilityNotHistory = refl",
        "publishedClaimNotAdmissible = refl",
        "sameItemDifferentGates = refl",
    ):
        assert token in source


def test_source_bounded_narrative_strata_are_separate():
    source = OWNER.read_text()
    for token in (
        "caseObservedLocalLink = Narrative.narrative-proposition",
        "Narrative.directlyEvidenced",
        "caseBoundedMethodInference = Narrative.narrative-proposition",
        "Narrative.boundedInference",
        "caseUnsupportedUnifiedCommand = Narrative.narrative-proposition",
        "Narrative.unsupported",
        "caseNarrativeStrata : List Narrative.NarrativeProposition",
        "caseStrataDoNotPromoteProgramme = refl",
    ):
        assert token in source


def test_page_inspected_primary_source_cuts_have_explicit_bounded_propositions():
    source = OWNER.read_text()
    roadmap = ROADMAP.read_text()
    for token in (
        'sclCALicensingOralEvidence : CaseClaim',
        'delaware2013FTCEntityFinding : CaseClaim',
        'caVersusCIAWitnessClarification : CaseClaim',
        'bannonScheduledBreakfast2019 : CaseClaim',
        'bannonOctober2018Messages : CaseClaim',
        'epsteinEstateScheduleRoot : OriginRoot',
        'https://committees.parliament.uk/oralevidence/7803/html/ ; Q1273',
        'https://www.ftc.gov/system/files/documents/cases/d09389_comm_final_opinionpublic.pdf',
        'https://oversightdemocrats.house.gov/imo/media/doc/epstein-production-3rd-tranch_456.pdf',
        'Q1458-Q1459',
        'oralLicensingSource = bounded-source',
        'ftcDelawareEntitySource = bounded-source',
        'estateBannonScheduleSource = bounded-source',
        'bannonOctober2018MirrorSource = bounded-source',
        'EFTA01615409',
        'observedScheduleOutcome = listedOnly',
        'listedAppointmentNotConfirmedMeeting = refl',
        'correctedAcronymIsCA = refl',
        'correctedAcronymIsNotCIA ()',
        'wylieOralOrigin :',
        'wylieWrittenOrigin :',
        'differentDescriptionsRequireOriginalAgreements ()',
        'descriptionsDoNotResolveContractIdentity ()',
    ):
        assert token in source
    for key in (
        '### Acquired primary-source cut',
        'December 2013',
        'PDF page 2 (index 1)',
        'Q1458–1459',
        'FTC decision followed CA\'s default',
        'H3 (specified coordinated',
    ):
        assert key in roadmap


def test_wylie_repeat_evidence_and_schedule_never_pay_hidden_network():
    source = OWNER.read_text()
    # Multiple statements with the same origin root do not create independent witnesses.
    assert 'bounded-source sclCALicensingOralEvidence wylieRoot' in source
    assert 'bounded-source caVersusCIAWitnessClarification wylieRoot' in source
    assert 'wylieWrittenOrigin :\n    SourceStatementOrigin wylieWritten2018 wylieRoot' in source
    assert 'wylieOralOrigin :\n    SourceStatementOrigin wylieOral2018 wylieRoot' in source
    assert 'true false false false' in source
    assert 'caseWholeH2Unpaid = refl' in source
    assert 'caseCovertH3Unpaid = refl' in source
    assert 'listedAppointmentNotConfirmedMeeting = refl' in source

def test_bannon_2018_mirror_remains_derivative_carrier_not_new_witness():
    source = OWNER.read_text()
    roadmap = ROADMAP.read_text()
    assert 'bounded-source bannonOctober2018Messages epsteinCorrespondenceRoot' in source
    assert 'journalist-hosted four-page reproduction' in source.lower()
    assert 'exact DOJ-native custody and complete surrounding thread were not checked' in source
    assert 'true false false false' in source
    assert 'Poder360-hosted DOJ-labelled' in roadmap
    assert 'not a new witness or an independently retrieved DOJ original' in roadmap


def test_three_independent_legal_objects_are_not_one_universal_ip_bridge():
    source = OWNER.read_text()
    for token in (
        "ftcServicesAndLicencesDescribed : CaseClaim",
        "fecDecember2013LLCStatement : CaseClaim",
        "fecForeignNationalReasonToBelieve : CaseClaim",
        "fecCaseClosedWithoutFinalLiability : CaseClaim",
        "fecEnforcementRoot : OriginRoot",
        "gsrSCLDataSubscription : CorporateInstrument",
        "sclCAOperatingServices : CorporateInstrument",
        "sclCAIPLicence : CorporateInstrument",
        "gsr2014Agreement = instrument-source-receipt",
        "sclCAServiceAgreement = instrument-source-receipt",
        "sclCAIPAgreement = instrument-source-receipt",
        "canonicalInstrumentStack : List InstrumentSourceReceipt",
        "ftcAgreementNotOriginalSignedInstrument = refl",
        "sclCAOperatingAgreementNotAquinoMethod = refl",
        "sclCAIPLicenceNotEpsteinDataset = refl",
    ):
        assert token in source


def test_fec_preliminary_enforcement_and_register_same_origin():
    source = OWNER.read_text()
    roadmap = ROADMAP.read_text()
    for token in (
        "fecCorporateDate = date-and-source-role",
        "ftcCorporateDate = date-and-source-role",
        "counselMemoDate = date-and-source-role",
        "uninspectedCharterCannotSettleDifferentLegalActs = refl",
        "fecReasonToBelieveReceipt = fec-stage-receipt",
        "fecClosureReceipt = fec-stage-receipt",
        "fecReasonToBelieveNotFinalGuilt = refl",
        "fecClosureDoesNotRewriteOriginalFindings = refl",
        "https://www.fec.gov/files/legal/murs/7382/7382_33.pdf",
        "https://www.fec.gov/data/legal/matter-under-review/7351/",
    ):
        assert token in source
    assert "### FTC/FEC cross-source contract and enforcement resolution" in roadmap
    assert "FTC **default-based** privacy/deception liability" in roadmap
    assert "two agencies quoting the same registry" in roadmap
    assert "31 Dec 2013" in roadmap
    assert "4 June 2014" in roadmap
    assert "5–0 to close the file" in roadmap


def test_wylie_senate_hacking_claim_is_not_independent_kompromat_proof():
    source = OWNER.read_text()
    roadmap = ROADMAP.read_text()
    for token in (
        "wylieKompromatStatement2018 : CaseClaim",
        "wylieProjectRiponStatement2018 : CaseClaim",
        "bounded-source wylieKompromatStatement2018 wylieRoot",
        "bounded-source wylieProjectRiponStatement2018 wylieRoot",
        "wylieSenateOrigin :",
        "SourceStatementOrigin wylieSenateMay2018 wylieRoot",
        "wylieAllegedSCLBlackOps = bounded-source",
        "wylieRiponStatement = bounded-source",
        "canonicalKompromatCut = alleged-kompromat-programme-cut",
        "testimonyDoesNotProveBannonHackingDirection = refl",
        "kompromatMethodDoesNotJoinEpsteinNetwork = refl",
        "witnessReportingDoesNotPayIntelligenceCommand = refl",
    ):
        assert token in source
    for phrase in (
        "### SCL kompromat allegation:",
        "PDF page 4 (index 3), paragraph 15",
        "PDF page 5 (index 4), paragraph 19",
        "one underlying witness/source-origin family",
        "exact Epstein same-object tasking = UNPAID",
    ):
        assert phrase in roadmap


def test_ripon_has_separate_witness_and_committee_origins():
    source = OWNER.read_text()
    roadmap = ROADMAP.read_text()
    for token in (
        "silvesterTestimonyRoot : OriginRoot",
        "dcmsCommitteeFinalReportRoot : OriginRoot",
        "parliamentaryCommitteeFinding : SourceRole",
        "silvesterAIQRiponDevelopment2018 : CaseClaim",
        "silvesterAIQBoltonDeployment2018 : CaseClaim",
        "dcmsRiponRepositoryReview2019 : CaseClaim",
        "dcmsICOBrexitCounterFinding2019 : CaseClaim",
        "bounded-source silvesterAIQRiponDevelopment2018 silvesterTestimonyRoot",
        "bounded-source dcmsRiponRepositoryReview2019 dcmsCommitteeFinalReportRoot",
        "silvesterRiponEvidence = bounded-source",
        "dcmsRiponProjectReport = bounded-source",
        "localRiponObject = scoped-ripon-object-payment",
        "localH2ProgrammeObjectPaid = refl",
        "localRiponDeveloperToSCLRelationPaid = refl",
        "riponSourceTreeNotInCaseCustody = refl",
        "riponPersonalBannonCodeControlUnpaid = refl",
        "riponDoesNotPromoteAquinoLink = refl",
        "riponDoesNotPromoteEpsteinLink = refl",
        "localRiponH2NotGlobalH3 = refl",
        "scopedH2DoesNotChangeWholeNetworkH2 = refl",
    ):
        assert token in source
    for token in (
        "### Ripon: an actual local H2",
        "Q2776–2784",
        "Q2949–2955",
        "scl.ripon.us",
        "no H2 anywhere",
        "local technical subcluster",
        "Whole-network H2",
    ):
        assert token in roadmap


def test_ripon_direct_corporate_contract_not_inferred_from_code_crossing():
    source = OWNER.read_text()
    roadmap = ROADMAP.read_text()
    assert "not unauthorized influence, CA contractual privity" in source
    assert "unauthorized influence" in source
    assert "original code bytes" in source.lower() or "original code" in source.lower()
    assert "silvesterAIQBoltonDeployment2018" in source
    assert "Direct contractual link **disputed/denied by Silvester**" in roadmap


def test_ripon_independent_nix_and_kogan_origins_without_false_dataset_join():
    source = OWNER.read_text()
    roadmap = ROADMAP.read_text()
    for token in (
        "nixWitnessRoot : OriginRoot",
        "koganWitnessRoot : OriginRoot",
        "nixAIQHistoricalRiponConfirmation : CaseClaim",
        "koganSeparateStatisticalDelivery : CaseClaim",
        "bounded-source nixAIQHistoricalRiponConfirmation nixWitnessRoot",
        "bounded-source koganSeparateStatisticalDelivery koganWitnessRoot",
        "data RiponRole : Set where",
        "silvesterRole = ripon-role-statement",
        "nixRole = ripon-role-statement",
        "koganRole = ripon-role-statement",
        "silvesterNamesRipon = refl",
        "nixNamesRipon = refl",
        "koganDeliveryDoesNotPayDirectAIQKnowledge = refl",
        "originalDatasetFingerprintStillUnpaid = refl",
    ):
        assert token in source
    for token in (
        "### Independent witnesses at the Ripon boundary",
        "Q3259–Q3266",
        "Q2012–Q2018",
        "MUR7350_24",
        "full file-level GSR→Ripon identity is NOT verified",
    ):
        assert token in roadmap


def test_reporting_roots_distinguish_original_upguard_vickery_from_dcms_derivative():
    source = OWNER.read_text()
    roadmap = ROADMAP.read_text()
    for token in (
        "upguardVickeryResearchRoot : OriginRoot",
        "guardianInterviewReportingRoot : OriginRoot",
        "apInvestigativeReviewRoot : OriginRoot",
        "riponSourceCodePublicExposure2018 : CaseClaim",
        "bannonEpsteinVideoPublished2026 : CaseClaim",
        "associatedPressBlackmailCounterReview2026 : CaseClaim",
        "bounded-source riponSourceCodePublicExposure2018 upguardVickeryResearchRoot",
        "bounded-source bannonEpsteinVideoPublished2026 guardianInterviewReportingRoot",
        "bounded-source associatedPressBlackmailCounterReview2026 apInvestigativeReviewRoot",
        "upguardRiponCodeReportingCut = external-object-evidence-cut",
        "bannonFilmedInterviewReportingCut = external-object-evidence-cut",
        "associatedPressContraryReviewCut = external-object-evidence-cut",
        "riponTechnicalRootShared = refl",
    ):
        assert token in source
    for token in (
        "### Reporting audit and root-lineage correction (2026-10-24)",
        "UpGuard, 26 Mar 2018",
        "Ripon_canvas",
        "Ripon_dialer",
        "Same underlying repository/acquisition",
        "Associated Press review, 8 Feb 2026",
        "14 hours of different Epstein video clips",
    ):
        assert token in roadmap


def test_video_and_press_reporting_are_not_native_bytes_or_tasking():
    source = OWNER.read_text()
    roadmap = ROADMAP.read_text()
    for token in (
        "upguardBlogIsNotOriginalGitTree = refl",
        "newsOfFilmIsNotOriginalFootage = refl",
        "filmedInterviewNotCovertTasking = refl",
        "pressReviewDoesNotProveUniversalAbsence = refl",
        "videoCompilationIsNotBannonReel ()",
        "Bannon-Epstein interview",
        "originalNativeObjectHeldByThisPR : Bool",
        "broaderIntelligenceProgrammePaid : Bool",
    ):
        assert token in source
    assert "Only use documentary segments relevant to inquiry" in roadmap
    assert "Do not attempt retrieval of exposed personal records, passwords or secret keys" in roadmap
    assert "AP's contrary review" in roadmap


def test_bannon_filming_already_paid_in_original_owner_not_rediscovered():
    original = PRIOR_FILM_OWNER.read_text()
    source = OWNER.read_text()
    for token in (
        "bannonCorrespondenceReceipt : BridgeReceipt",
        "bannonMediaRehabReceipt : BridgeReceipt",
        "bannonPoliticalMessagingReceipt : BridgeReceipt",
        "bannonInternationalStrategyReceipt : BridgeReceipt",
        "Released texts and video show Bannon advising Epstein",
        "bannonFilmingAlreadyPaid = refl",
        "videoExistenceDebtRetired = refl",
    ):
        assert token in original
    for token in (
        "bannonExistingProductionChain = BannonBridge.canonicalBannonMediaProductionFrontier",
        "preExistingFilmedInterviewIsPaid = refl",
        "preExistingAprilCounselLetterLocated = refl",
        "preExistingJulyShootingMessagesLocated = refl",
    ):
        assert token in source


def test_canonical_bannon_production_source_chain_and_legal_limits():
    original = PRIOR_FILM_OWNER.read_text()
    roadmap = ROADMAP.read_text()
    for token in (
        "indyke2019LetterEvidence = bannon-production-evidence",
        "juneJulyProductionMessagesEvidence = bannon-production-evidence",
        "existingFilmEvidence = bannon-production-evidence",
        "EFTA00809863-EFTA00809866",
        "House Oversight 027794-027848",
        "letterLocatedButExecutionOpen = refl",
        "letterCannotByItselfCreateLegalPrivilege = refl",
        "july6ProposedShootNotCompletedShoot = refl",
        "letterAndMessageDoNotIdentifyFilmReel = refl",
        "exactFilmReelObjectStillUnpaid = refl",
        "legalEngagementCannotBePromotedToExecuted = refl",
        "filmCannotBePromotedToIntelligenceDirection = refl",
    ):
        assert token in original
    for token in (
        "### Bannon–Epstein filming: existing-owner audit",
        "EFTA00809863–EFTA00809866",
        "HOUSE_OVERSIGHT_027794–027848",
        "existence of filmmaking (paid before #1245)",
        "DOJ PDF page images not accessible",
        "source root for the April letter is its author/producer",
    ):
        assert token in roadmap


def test_unpaid_deduplicated_case_reel_join_stays_narrow():
    source = OWNER.read_text()
    for token in (
        "actualSignedAgreementStillUnverified = refl",
        "reelBytesHashStillUnverified = refl",
        "bannonWorkProductCut = case-dependency-cut",
        "April 3 2019 EFTA00809863-Indyke letter located",
        "Prior owner pays filmed interview",
        "dated Jun-Jul 2019 House shoot messages",
        "preExistingFilmedInterviewIsPaid = refl",
        "caseWholeH2Unpaid = refl",
        "caseCovertH3Unpaid = refl",
    ):
        assert token in source
    assert "not a verified signed/accepted contract" not in source  # forbid fabricated acceptance


def test_black_epstein_existing_transaction_chain_is_reused_not_reauthored():
    source = OWNER.read_text()
    for owner in (
        "EpsteinBlackAgreementInvoiceWorkJoin20261015Exact as BlackWork",
        "EpsteinBlackInvoiceWireSettlement20261015Exact as BlackWire",
        "EpsteinBlackApolloSameObjectReceiptRound20261014Exact as BlackApollo",
    ):
        assert owner in source
    for token in (
        "blackPreExistingAgreementWork = BlackWork.canonicalWorkJoinBoundary",
        "blackPreExistingSettledWire = BlackWire.canonicalWireBoundary",
        "blackPreExistingApolloNuance = BlackApollo.canonicalApolloNuanceBoundary",
        "blackServicesDocumented = refl",
        "blackInvoiceDocumented = refl",
        "black2014InvoiceAndReceiptMatched = refl",
        "blackPaymentNotIdentifiedAsChecklistFee = refl",
        "blackInvoiceAndWireNotMeasuredTaxBenefit = refl",
        "apolloNeverAutomaticallyBannonPayer = refl",
        "bannonFilmAlreadyEstablishedByDifferentOwner = refl",
        "bannonOriginalReelHashNotReplacedByBlackReceipts = refl",
        "blackPaymentDoesNotCreateBannonFilmFunding ()",
        "blackPaymentDoesNotCreateUnifiedProgramme ()",
    ):
        assert token in source


def test_film_needs_only_receipt_hash_and_optional_transcript():
    prior = PRIOR_FILM_OWNER.read_text()
    for token in (
        "canonicalLightweightFilmObjectReceipt = lightweight-film-object-receipt",
        "docs/research/bannon-epstein-video-manifest-20261024.json",
        "videoNeedNotBeVendored = refl",
        "noUncomputedSHA256Fabrication = refl",
        "chapterTimestampsNotVerbatimTranscript = refl",
        "noTranscriptClaimWithoutBytes = refl",
        "reelToAgreementJoinNotConferredByHash = refl",
    ):
        assert token in prior


def test_wyden_march2026_assertions_are_not_adjudicated_or_film_custody():
    root = ROOT / "DASHI/Cognition/EpsteinBlackApolloSameObjectReceiptRound20261014Exact.agda"
    source = root.read_text()
    for token in (
        "wydenWomenPaymentsQuestion = wyden-2026-claim-receipt",
        "wydenSurveillanceQuestion = wyden-2026-claim-receipt",
        "wydenCompensationComparator = wyden-2026-claim-receipt",
        "wydenGiftTaxQuestion = wyden-2026-claim-receipt",
        "wydenClaimIsNotAdjudication = refl",
        "wydenSurveillanceClaimNotBannonFilmEvidence = refl",
        "wydenOriginalMessageStillUninspectedHere = refl",
        "EFTA00977823",
    ):
        assert token in source


def test_exact_doj_efta01600824_transcript_locator_paid_but_sha_open():
    source = OWNER.read_text()
    original = PRIOR_FILM_OWNER.read_text()
    roadmap = ROADMAP.read_text()
    for token in (
        "bannonOriginalReelIndex = located-video-transcript-index",
        "EFTA01600824.mov",
        "dojReelIdentifierLocated = refl",
        "publishedTimecodedTranscriptLocated = refl",
        "dojReelHashStillUncomputed = refl",
        "transcriptWithoutReviewNotCertified = refl",
        "originalReelIdDoesNotPay2019ContractJoin = refl",
    ):
        assert token in original
    for token in (
        "bannonIdentifiedDOJReelIndex = BannonBridge.bannonOriginalReelIndex",
        "bannonDOJIdentifierNowLocated = refl",
        "bannonTimecodedTranscriptNowLocated = refl",
        "bannonDOJHashStillUnverified = refl",
    ):
        assert token in source
    for token in (
        "### Lightweight film provenance: real DOJ identifier",
        "1,753",
        "EFTA01600824.mov",
        "sha256: null",
        "scripts/hash_media_receipt.py",
        "publicly indexed timecoded ASR transcript",
    ):
        assert token in roadmap


def test_transcript_as_research_acceptance_gate():
    original = PRIOR_FILM_OWNER.read_text()
    case = OWNER.read_text()
    assert "transcriptSufficientForThisResearchCut = refl" in original
    assert "videoHashNotAnAcceptanceGate = refl" in original
    assert "noBlackTransactionFromInterviewSpeech = refl" in original
    assert "canonicalTranscriptContentCuts : List TimecodedTranscriptReceipt" in original
    assert "bannonTranscriptNowAdequateForResearch = refl" in case
    assert "bannonFilmSHAIsNotBlocking = refl" in case
    assert "bannonTranscriptNotBlackPaymentEvidence = refl" in case


def test_transcript_independent_chronology_not_personal_confirmations():
    original = PRIOR_FILM_OWNER.read_text()
    roadmap = ROADMAP.read_text()
    for token in (
        "santaFeOfficialHistory = historical-source-comparator",
        "fdic2008OriginalTimeline = historical-source-comparator",
        "epsteinSelfBiographicalRecord = historical-source-comparator",
        "early1990sSFIClaimIsNot1984Founding = refl",
        "officialFinancialTimelineIsNotJailCallLog = refl",
        "promotionalBioNotIndependentInstitution = refl",
        "stagedOffCameraInterview = timecoded-transcript-receipt",
        "donorEthicsLegalityExchange = timecoded-transcript-receipt",
    ):
        assert token in original
    for token in (
        "May 1984",
        "15 September 2008",
        "EFTA00304519",
        "### EFTA01600824 transcript-first content audit",
    ):
        assert token in roadmap


def test_black_2026_congress_primary_records_reuse_canonical_owners():
    """Source-written structural checks; not a substitute for Agda kernel proof."""
    black = (ROOT / "DASHI/Cognition/EpsteinBlackApolloSameObjectReceiptRound20261014Exact.agda").read_text()
    consumer = OWNER.read_text()
    source = (ROOT / "docs/research/aquino-epstein-surrounding-prior-art-audit-20261024.md").read_text()

    for token in (
        "blackJuneInterview2026 = black-2026-source-receipt",
        "blackCommitteeReport119831 = black-2026-source-receipt",
        "blackHouseResolution1543 = black-2026-source-receipt",
        "blackDechertSECOriginal2021 = black-2026-source-receipt",
        "blackApolloProxyConflicts2021 = black-2026-source-receipt",
        "canonicalBlack2026HouseBoundary = black-2026-house-boundary",
        "originalHouseTranscriptPaid = refl",
        "witnessAwarenessDoesNotEstablishNegotiation = refl",
        "signedNDAObjectStillMissing = refl",
        "contemptReferralNotConviction = refl",
        "directorPastEmploymentNotTasking = refl",
        "black2026HouseDoesNotPayBannonFunding = refl",
        "black2026HouseDoesNotPayWholeNetworkH3 = refl",
        "H. Rept. 119-831",
        "H. Res. 1543",
        "2026-06-26",
    ):
        assert token in black
    for token in (
        "black2026OriginalCongressionalCase =",
        "BlackApollo.canonicalBlack2026HouseBoundary",
        "originalBlackInterviewAndHouseDispositionLocated = refl",
        "house2026NDAContractBytesRemainUninspected = refl",
        "house2026CommitteeIsNotTransactionReconciliation = refl",
        "house2026PastCIAOfficeNotPresentDirection = refl",
        "house2026DoesNotPayBannonProgrammeBridge = refl",
        "house2026DoesNotPayCaseWideCommand = refl",
    ):
        assert token in consumer
    for token in (
        "ProvenanceClosureIndependenceExact",
        "IbrahimSnowballParetoFrontierExact",
        "2015 settlement/NDA",
        "Apollo 2021 SEC DEF14A",
        "H. Rept. 119-831",
        "House vote text",
    ):
        assert token in source


def test_house_source_families_are_not_double_counted_or_promoted():
    black = (ROOT / "DASHI/Cognition/EpsteinBlackApolloSameObjectReceiptRound20261014Exact.agda").read_text()
    audit = (ROOT / "docs/research/aquino-epstein-surrounding-prior-art-audit-20261024.md").read_text()
    assert "report is not a second independent witness" in black
    assert "Black's 2026 restatement is not a second review" in audit
    assert "Past CIA employment is not evidence" in audit
    assert "criminal contempt conviction" in audit
    assert "executed2015NDABytesInspected : Bool" in black
    assert "committeeContemptIsCriminalConviction : Bool" in black
    assert "caseWideCovertCommandEstablished : Bool" in black


def test_black_sdny_oct2026_order_is_not_ddc_congress_challenge_disposition():
    black = (ROOT / "DASHI/Cognition/EpsteinBlackApolloSameObjectReceiptRound20261014Exact.agda").read_text()
    consumer = OWNER.read_text()
    audit = (ROOT / "docs/research/aquino-epstein-surrounding-prior-art-audit-20261024.md").read_text()
    for symbol in (
        "independentJudicialDocketEvent : Black2026EvidenceRole",
        "blackHouseSubpoenaChallengeDocket = black-2026-source-receipt",
        "blackDoeOctoberDismissalOriginalOrder = black-2026-source-receipt",
        "blackDoeNotHouseChallenge ()",
        "voluntaryDismissalNotTrialFinding = refl",
        "feesMotionNotResolvedByDismissal = refl",
        "separateDocketNotResolvedByDoeDismissal = refl",
        "ddcFinalDispositionStillUnverified = refl",
        "23-cv-6418",
        "1:26-cv-03084",
    ):
        assert symbol in black
    for symbol in (
        "BlackApollo.canonicalBlack2026DistinctCourtCaseBoundary",
        "blackDoeOrderNotHouseCaseDisposition = refl",
        "blackDoeDismissalNotMeritsTrialFinding = refl",
        "ddcHouseSubpoenaJudgmentNotYetVerified = refl",
    ):
        assert symbol in consumer
    assert "fees motion (ECF 440)" in audit
    assert "at the plaintiff's request" in audit
    assert "D.D.C." in audit and "S.D.N.Y." in audit


def test_chain_reaction_is_existing_banking_owner_lead_not_criminal_finding():
    banking = (ROOT / "DASHI/Cognition/EpsteinBankingInfrastructureAcquisitionExact.agda").read_text()
    case = OWNER.read_text()
    for token in (
        "chainReaction2015Memo = chain-reaction-source-receipt",
        "chainReactionThirdPartyIndex = chain-reaction-source-receipt",
        "chainReactionWyden2026Questions = chain-reaction-source-receipt",
        "EFTA00173953", "NY-NYS-0829", "OFC-TP-15-12392",
        "memoLeadOnlyCaveatRetained : Bool",
        "nativeMemoScanPageAuthenticated : Bool",
        "namedBankWireMatchedToExistingLedger : Bool",
        "investigationTerminationMotiveProven : Bool",
        "chainReactionLeadNotAdjudication = refl",
        "chainReactionTerminationNotEstablished = refl",
        "chainReactionNoAutoBlackLedgerJoin = refl",
        "chainReactionNoGlobalProgrammeTransfer = refl",
    ):
        assert token in banking
    for token in (
        "import DASHI.Cognition.EpsteinBankingInfrastructureAcquisitionExact as Banking",
        "chainReactionFinanceOriginalOwner = Banking.canonicalChainReactionPromotionBoundary",
        "chainReaction2015MemoSourceIdentified = refl",
        "chainReactionInvestigationNotAdjudication = refl",
        "chainReactionStillNeedsTransactionFingerprint = refl",
        "chainReactionNoBlackNDAShortcut = refl",
        "chainReactionNoUnifiedCaseProgramme = refl",
    ):
        assert token in case


def test_ripon_intermediary_countermodel_stops_unsigned_contract_promotion():
    case = OWNER.read_text()
    for token in (
        "silvesterWrittenOriginal2018 = ripon-independent-chain-evidence",
        "dcmsRiponOCEANReview2019 = ripon-independent-chain-evidence",
        "koganSeparateDelivery2018 = ripon-independent-chain-evidence",
        "ftcOriginalCorporateContracts2019 = ripon-independent-chain-evidence",
        "FKN0086",
        "90210/html/",
        "committees.parliament.uk/oralevidence/7853/html/",
        "RiponIntermediaryCountermodel",
        "canonicalRiponIntermediaryCountermodel =",
        "riponSCLContractAndReportedCAEcosystemFlowCompatible = refl",
        "riponCommitteeDataFlowIsNotSignedCAContract = refl",
        "riponNamedKoganOutputToAIQImportStillUnpaid = refl",
        "riponDoesNotCreateAquinoTransfer2026 = refl",
        "riponDoesNotCreateBannonEpsteinMediaUse2026 = refl",
    ):
        assert token in case
    assert "silvesterWritten2018" in case and "dcmsReport2019" in case


def test_portfolio_maxcut_is_multi_lane_not_black_nda_centric():
    portfolio = (ROOT / "docs/research/aquino-epstein-portfolio-maxcut-20261024.md").read_text()
    roadmap = ROADMAP.read_text()
    for token in (
        "AIQ–SCL–CA technical operation",
        "Banking + OCDETF original programme",
        "Bannon–Epstein media production",
        "Black 2015 NDA and financial service scope",
        "Maxwell/PROMIS",
        "Aquino–SCL technique genealogy",
        "Cross-network covert hierarchy H2/H3",
        "source-state countermodel",
        "not a finished investigative product",
        "FKN0086",
        "EFTA00173953",
    ):
        assert token in portfolio
    assert "aquino-epstein-portfolio-maxcut-20261024.md" in roadmap


def test_canadian_ripon_sworn_testimony_does_not_promote_score_producer():
    case = OWNER.read_text()
    portfolio = (ROOT / "docs/research/aquino-epstein-portfolio-maxcut-20261024.md").read_text()
    for token in (
        "riponSilvesterCanadian113 = ripon-pipeline-testimony",
        "riponMassinghamCanadian117 = ripon-pipeline-testimony",
        "ETHI-113 2018-06-12",
        "ETHI-117 2018-09-27",
        "RiponScoreProducerDisplayBoundary",
        "canonicalRiponScoreProducerDisplayBoundary =",
        "riponScoreDisplayPaidAsWitnessStatement = refl",
        "riponSCLSupplierClaimPreserved = refl",
        "riponNoProducerAttributionWithoutDataset = refl",
        "riponScoreDisplayDoesNotCertifyFacebookOrigin = refl",
        "riponScoreDisplayNoElectionOutcomeProof = refl",
    ):
        assert token in case
    for token in (
        "score-file version",
        "distinct individual source",
        "page-image screenshot requests returned a 403",
        "exact dataset fingerprint is still open",
    ):
        assert token in portfolio


def test_crosspollination_reuses_original_generic_proof_carriers():
    case = OWNER.read_text()
    readme = (ROOT / "docs/research/aquino-epstein-crosspollination-phase-decision-20261025.md").read_text()
    for import_line in (
        "import DASHI.Core.SourceAcquisitionGeometryExact as Acquisition",
        "import DASHI.Core.EventTimeCapabilityAlignmentBidiExact as EventTime",
        "import DASHI.Culture.MissingDeceasedCommonObjectProgrammeDiscriminatorExact as Common",
        "import DASHI.Cognition.EpsteinBlackPaymentScopeReconciliation20261014Exact as BlackScope",
    ):
        assert import_line in case
    for token in (
        "ftcGSRSCLCommissionSource = Acquisition.sourceAcquisitionTarget",
        "ocdetfOriginalDocumentAcquisition = Acquisition.sourceAcquisitionTarget",
        "ftcPrimaryInspectionPaid = refl",
        "ocdetfOriginalPageInspectionStillUnpaid = refl",
        "canonicalSCLTwoArmExactObjectCut = scl-two-arm-exact-object-cut",
        "ftcGSRContractAndRiponInterfaceBothLocated = refl",
        "sharedSCLHubDoesNotProveSpecificDataset = refl",
        "threeDifferentFTCContractsDoNotCreateDirectAIQCAContract = refl",
        "sclProgrammeDoesNotProveAquinoOriginalTechnique = refl",
        "sclProgrammeDoesNotProveBannonEpsteinReuse = refl",
        "localNamedRiponWitnesses = Common.cross-person-programme-receipt",
        "bannonBlackProgrammeNonJoin = Common.cross-person-programme-receipt",
        "localRiponNamesDoNotPayWholeCommand = refl",
        "gsrSCL2014ContractTime = EventTime.event-time-capability-receipt",
        "bannonEpstein2019ProductionTime = EventTime.event-time-capability-receipt",
        "blackExistingScopeReconciliation = BlackScope.canonicalScopeReconciliation",
        "blackScopeDifferenceDoesNotResolveOCDETF = refl",
        "black2016TransactionClassificationStillOpen = refl",
        "canonicalFinanceInvestigationJoinBoundary =",
        "financialEventTimeOverlapNotTransactionIdentity = refl",
        "unverifiedOCDETFOutcomeIsNotSuppression = refl",
        "two2015RecordsDoNotCreateNDAJoin = refl",
    ):
        assert token in case
    for token in (
        "FTC's legal findings",
        "two-arm intermediary/lineage problem",
        "SourceAcquisitionGeometryExact",
        "EventTimeCapabilityAlignmentBidiExact",
        "CrossPersonProgrammeReceipt",
        "SCLTwoArmExactObjectCut",
    ):
        assert token in readme or token in case


def test_crosspollination_source_roots_and_hypothesis_gates():
    portfolio = (ROOT / "docs/research/aquino-epstein-portfolio-maxcut-20261024.md").read_text()
    report = (ROOT / "docs/research/aquino-epstein-crosspollination-phase-decision-20261025.md").read_text()
    for token in (
        "June 4 2014",
        "unopposed summary decision after CA default",
        "original version-labelled output file",
        "Black annual total is not proof",
        "2016 $6.3m",
        "Global H2/H3 gate",
        "Agda kernel",
    ):
        assert token in report
    assert "source-state countermodel" in portfolio
    assert "source-identical" in report


def test_ftc_final_order_is_duty_not_completed_deletion():
    case = OWNER.read_text()
    report = (ROOT / "docs/research/aquino-epstein-crosspollination-phase-decision-20261025.md").read_text()
    for token in (
        "record FTCDataCustodyOrderBoundary : Set where",
        "canonicalFTCDataCustodyOrderBoundary = ftc-data-custody-order-boundary",
        "recipientDisclosureSwornStatementRequired : Bool",
        "derivedDataAndWorkProductDeletionRequired : Bool",
        "regulatoryPreservationExceptionExplicit : Bool",
        "complianceStatementPersonallyInspectedHere : Bool",
        "dataDeletionCompletedAndIndependentlyVerified : Bool",
        "ftcCustodyOrderOfficiallyLocated = refl",
        "ftcRequiredDeletionNotProvedCompleted = refl",
        "ftcOrderDoesNotIdentifyRiponRows = refl",
        "ftcOrderDoesNotConvictThirdPartyPossessor = refl",
        "ftcRedactedComplianceRouteAccepted = refl",
        "ftc2019OriginalOrderSource = Acquisition.sourceAcquisitionTarget",
    ):
        assert token in case
    for token in (
        "original FTC Final Order",
        "sworn statement identifying recipients",
        "preservation exceptions",
        "order is not itself proof",
        "lawfully redacted",
    ):
        assert token in report


def test_canadian_2019_regulators_pay_aggregate_kogan_derived_aiq_scores():
    """Joint first-party regulator finding closes aggregate edge, not individual file custody."""
    case = OWNER.read_text()
    evidence = (ROOT / "docs/research/kogan-aiq-canadian-regulator-source-cut-20261025.md").read_text()
    for token in (
        "canadianJointAIQOriginal2019 = Acquisition.sourceAcquisitionTarget",
        "PIPEDA Findings 2019-004",
        "canonicalCanada2019AggregateScoreFinding = canada-2019-aggregate-score-finding",
        "sourceStatesScoresAtLeastPartlyDerivedFromKoganFacebookData : Bool",
        "investigatorsFoundAIQKnewSCLUsedKoganData : Bool",
        "investigatorsFoundUSCampaignConsentFailures : Bool",
        "investigatorsFoundInadequateSafeguardsAffectingAbout35m : Bool",
        "canadaRegulatorsPayAggregateKoganDerivedAIQScores = refl",
        "canadaRegulatorsPayAIQAwareness = refl",
        "canadaJointReportNotTwoIndependentRoots = refl",
        "canadaKoganRawAppBytesStillNotProvenAtAIQ = refl",
        "canadaAggregateFindingDoesNotPaySpecificRiponRow = refl",
        "canadaConditionalResolutionIsNotVerifiedFollowup = refl",
        "canadaScoreFindingDoesNotPayElectionCausality = refl",
        "canadaScoreFindingDoesNotPayEpsteinAquinoProgramme = refl",
        "canonicalTwoArmCanadianPromotionCut =",
        "aggregateSourceLineageNowPaid = refl",
        "regulatoryAggregateFindingDoesNotProvideOriginalRowHash = refl",
        "aggregateProvenanceIsNotSpecificConsumerDataIdentity = refl",
    ):
        assert token in case
    for token in (
        "The regulators",
        "one *joint* investigation",
        "derived at least in part",
        "specific",
        "raw",
        "conditionally resolved",
        "H2/H3",
    ):
        assert token.lower() in evidence.lower()


def test_canada_paid_aggregate_is_not_private_raw_data_or_proven_outcome():
    case = OWNER.read_text()
    portfolio = (ROOT / "docs/research/aquino-epstein-portfolio-maxcut-20261024.md").read_text()
    roadmap = ROADMAP.read_text()
    assert "specificGSRScoreFileEqualsRiponInput : Bool" in case
    assert "sharedSCLHubDoesNotProveSpecificDataset = refl" in case
    assert "individualKoganGSRScoreFileToNamedRiponRowMatched : Bool" in case
    assert "canadaAggregateFindingDoesNotPaySpecificRiponRow = refl" in case
    assert "two-arm-canadian-promotion-cut true true false false false" in case
    assert "kogan-aiq-canadian-regulator-source-cut-20261025.md" in roadmap
    assert "Kogan-derived AIQ lineage" in portfolio
    assert "P0 aggregate link source finding CLOSED" in roadmap
    assert "whole-network" in portfolio.lower()


def test_march_wyden_ocdetf_same_investigator_and_confidential_tip_claim_only():
    bank = (ROOT / "DASHI/Cognition/EpsteinBankingInfrastructureAcquisitionExact.agda").read_text()
    study = (ROOT / "docs/research/kogan-aiq-canadian-regulator-source-cut-20261025.md").read_text()
    for token in (
        "chainReactionWydenMarch18 = chain-reaction-source-receipt",
        "Wyden",
        "2026-03-18",
        "confidential tip",
        "canonicalChainReactionOversightAttributionCut =",
        "marchAllegationIsNotAuthenticatedIntervention = refl",
        "wydenFollowupsDoNotCreateIndependentSecondSource = refl",
        "ocdetfOutcomeNotProvenBySenateComplaint = refl",
    ):
        assert token in bank
    assert "same Wyden investigation root" in study
    assert "independently authenticated DOJ blocking instruction" in study


def test_canadian_score_finding_routes_through_canonical_ca_owner():
    ca = (ROOT / "DASHI/Cognition/BannonCambridgeAnalyticaInfluenceInfrastructureExact.agda").read_text()
    case = OWNER.read_text()
    for token in (
        "canadianJointPrivacyRegulatorAIQFinding : InfluenceEdgeKind",
        "canadianJointRegulatorAIQReceipt = influence-receipt",
        "PIPEDA Findings 2019-004",
        "true false false true",
        "∷ canadianJointRegulatorAIQReceipt",
    ):
        assert token in ca
    for token in (
        "canonicalCanadianAIQCAInfluenceOwner = CA.canadianJointRegulatorAIQReceipt",
        "canadianRegulatorFindingAlsoInCanonicalCAOwner = refl",
        "canadianSpecificTechniqueTransferNotPaidByRegulator = refl",
    ):
        assert token in case


def test_canadian_partial_security_remediation_and_exposed_credentials_not_35m_download():
    case = OWNER.read_text()
    study = (ROOT / "docs/research/kogan-aiq-canadian-regulator-source-cut-20261025.md").read_text()
    for token in (
        "record Canadian2019RemediationEvidenceCut : Set where",
        "regulatorsFoundGitLabExposedAccessKeys : Bool",
        "reportedExternalDatabasesHeldAbout35mPersons : Bool",
        "reportSaysResearcherDeniedDownloadingThoseExternalDatabases : Bool",
        "securitySafeguardsIssueDeclaredResolvedIn2019Report : Bool",
        "sourceReportsAIQSuppliedSwornDeletionAffidavit : Bool",
        "entireConsentAndRemediationInvestigationUnconditionallyClosed : Bool",
        "canonicalCanadian2019RemediationEvidenceCut = canadian-2019-remediation-evidence-cut",
        "canadian2019SecurityIssueAlreadyReportedResolved = refl",
        "canadian2019SwornAffidavitActuallyReported = refl",
        "canadianAffidavitIsNotGlobalCopyErasureCertification = refl",
        "canadianSecurityResolutionIsNotEntireInvestigationClosure = refl",
        "canadian35mDatabaseVulnerabilityNot35mKoganRecords = refl",
    ):
        assert token in case
    for token in (
        "did not download those databases",
        "sworn deletion affidavit",
        "security-safeguards issue as resolved",
        "the whole consent investigation",
        "canonical CA influence owner",
    ):
        assert token.lower() in study.lower()


def test_canonical_disposition_freezes_research_not_primary_evidence():
    """The only current acceptance ledger; historical source notes remain accessible."""
    root = ROOT / "docs/research"
    current = (root / "aquino-epstein-canonical-disposition-20261025.md").read_text()
    for fragment in (
        "STOP broad acquisition; CERTIFY and DISPOSE",
        "Kogan-derived scores reached AIQ in aggregate",
        "security-safeguards subissue resolved",
        "NOT ESTABLISHED",
        "P0 — certification and consistency",
        "Reopen trigger:",
        "newly produced **original, dated, independently attributable same-object artefact**",
        "Agda",
        "pytest",
        "#1200",
        "#1233",
    ):
        assert fragment in current
    for filename in (
        "aquino-maxwell-epstein-ca-maxcut-20261024.md",
        "aquino-epstein-portfolio-maxcut-20261024.md",
        "aquino-epstein-crosspollination-phase-decision-20261025.md",
        "black-epstein-congress-2026-pareto-snowball.md",
        "aquino-epstein-surrounding-prior-art-audit-20261024.md",
    ):
        old = (root / filename).read_text()
        assert old.startswith("# ")
        assert "CURRENT DISPOSITION — RESEARCH FREEZE (25 Oct 2026)" in old[:850]
        assert "aquino-epstein-canonical-disposition-20261025.md" in old[:850]


def test_canonical_source_state_snapshots_have_actual_boolean_field_alignment():
    """Check record values, not just nearby mentions of a \N{LATIN SMALL LETTER R}efl witness."""
    import re

    def read_bool_snapshot(text, record, instance, constructor):
        a = text.index(f"record {record} : Set where")
        b = text.index(f"open {record} public", a)
        fields = re.findall(r"^    (\w+) : Bool$", text[a:b], flags=re.MULTILINE)
        assert fields, f"{record} has no auditable Bool fields"
        pos = text.index(f"{instance} =", b)
        end = text.index("\n\n", pos)
        assignment = text[pos:end]
        assert constructor in assignment
        values = re.findall(r"\b(?:true|false)\b", assignment)
        assert len(values) == len(fields), (record, len(fields), len(values))
        return dict(zip(fields, values))

    case = OWNER.read_text()
    bank = (ROOT / "DASHI/Cognition/EpsteinBankingInfrastructureAcquisitionExact.agda").read_text()
    canada = read_bool_snapshot(
        case, "Canada2019AggregateScoreFinding",
        "canonicalCanada2019AggregateScoreFinding", "canada-2019-aggregate-score-finding"
    )
    assert canada["sourceStatesScoresAtLeastPartlyDerivedFromKoganFacebookData"] == "true"
    assert canada["canadianAndBCBodiesAreSingleJointSourceRoot"] == "true"
    assert canada["individualKoganGSRScoreFileToNamedRiponRowMatched"] == "false"
    assert canada["agencyFollowupConfirmedImplementedHere"] == "false"
    assert canada["paidCrossNetworkEpsteinAquinoDirection"] == "false"

    remediation = read_bool_snapshot(
        case, "Canadian2019RemediationEvidenceCut",
        "canonicalCanadian2019RemediationEvidenceCut", "canadian-2019-remediation-evidence-cut"
    )
    assert remediation["securitySafeguardsIssueDeclaredResolvedIn2019Report"] == "true"
    assert remediation["sourceReportsAIQSuppliedSwornDeletionAffidavit"] == "true"
    assert remediation["swornAffidavitIndependentlyVerifiesEveryPossibleDataCopyErased"] == "false"
    assert remediation["entireConsentAndRemediationInvestigationUnconditionallyClosed"] == "false"

    senate = read_bool_snapshot(
        bank, "ChainReactionOversightAttributionCut",
        "canonicalChainReactionOversightAttributionCut", "chain-reaction-oversight-attribution-cut"
    )
    assert senate["march2026FollowupOriginalLetterPublished"] == "true"
    assert senate["februaryAndMarchAreSeparateInvestigatorRoots"] == "false"
    assert senate["independentDEAInternalInterventionInstructionInspected"] == "false"
    assert senate["originalOperationFinalDispositionVerified"] == "false"


def test_senate_public_letters_do_not_claim_original_ocdetf_native_scan():
    bank = (ROOT / "DASHI/Cognition/EpsteinBankingInfrastructureAcquisitionExact.agda").read_text()
    for receipt in ("chainReactionWyden2026Questions", "chainReactionWydenMarch18"):
        start = bank.index(f"{receipt} = chain-reaction-source-receipt")
        block = bank[start:bank.index("\n\n", start)]
        assert "laterSenateInquiryInterpretation" in block
        assert "true false false" in block, receipt
        assert "true true false" not in block, receipt
    assert "chainReactionNativeScanVerifiedHere : Bool" in bank


def test_original_ftc_kogan_nix_consents_and_uk_aiq_finance_use_canonical_ca_owner():
    ca = (ROOT / "DASHI/Cognition/BannonCambridgeAnalyticaInfluenceInfrastructureExact.agda").read_text()
    case = OWNER.read_text()
    for token in (
        "ftcKoganNixSeparateIndividualConsents : InfluenceEdgeKind",
        "ukElectoralAIQActualCampaignPayments : InfluenceEdgeKind",
        "ftcKoganNixIndividualConsentReceipt = influence-receipt",
        "ukElectoralAiqPaymentsReceipt = influence-receipt",
        "C-4693 (Kogan) / C-4694 (Nix)",
        "GBP675315.18",
        "Grimes successfully appealed",
        "∷ ftcKoganNixIndividualConsentReceipt",
        "∷ ukElectoralAiqPaymentsReceipt",
    ):
        assert token in ca
    for token in (
        "ftcKoganNixConsentCanonicalOwner = CA.ftcKoganNixIndividualConsentReceipt",
        "ukAIQPaymentCanonicalOwner = CA.ukElectoralAiqPaymentsReceipt",
        "canonicalOriginalElectionRegulatorySplit =",
        "ukElectoralAiqPaymentsExistAtRegulatorScope = refl",
        "koganFTCConsentDoesNotAdmitComplaintAllegations = refl",
        "grimesSanctionNotStillInForce = refl",
        "campaignPaymentsDoNotIdentifyGSRInputFile = refl",
        "ukLeaveEUNoProvenDirectCAContract = refl",
        "campaignRecordsDoNotPayCaseWideCovertCommand = refl",
    ):
        assert token in case


def test_pareto_ibrahim_stop_condition_and_original_appeal_are_reported():
    report = (ROOT / "docs/research/aquino-epstein-canonical-disposition-20261025.md").read_text()
    for token in (
        "Kogan C-4693",
        "Nix C-4694",
        "neither admitted nor denied",
        "GBP 675,315.18",
        "GBP 50,000",
        "GBP 100,000",
        "July 19, 2019",
        "GBP 61,000",
        "Leave.EU",
        "no evidence at that time",
        "Ibrahim/snowball",
        "source root fails to move an acceptance gate",
        "Saturated",
    ):
        assert token in report


def test_us_personal_consents_do_not_multiply_into_private_facebook_dataset_custody():
    case = OWNER.read_text()
    assert "personalFTCOrdersAreAdjudicatedAdmissionOfComplaint : Bool" in case
    assert "executedComplianceDeclarationsExaminedHere : Bool" in case
    assert "uk2016AIQInvoicesIdentifyGSRScoreFile : Bool" in case
    assert "sourcePaysEpsteinAquinoCommonCommand : Bool" in case
    assert "original-election-regulatory-split" in case


def test_original_ftc_v_bannon_2020_four_distinct_roles_and_no_guilt_promotion():
    ca = (ROOT / "DASHI/Cognition/BannonCambridgeAnalyticaInfluenceInfrastructureExact.agda").read_text()
    case = OWNER.read_text()
    for marker in (
        "ftc2020BannonCivilDemandInvestigation : InfluenceEdgeKind",
        "ftc2020BannonJudicialShowCauseOrder : InfluenceEdgeKind",
        "ftc2020BannonCIDPetitionReceipt = influence-receipt",
        "ftc2020BannonRespondentOppositionReceipt = influence-receipt",
        "ftc2020BannonJudicialShowCauseReceipt = influence-receipt",
        "ftc2020BannonReplyReceipt = influence-receipt",
        "1:20-mc-00111-CRC",
        "original independent opposing litigant pleading",
        "same FTC prosecutor root",
        "signed original federal judicial PROCEDURAL order",
        "∷ ftc2020BannonCIDPetitionReceipt",
        "∷ ftc2020BannonJudicialShowCauseReceipt",
        "∷ ftc2020BannonRespondentOppositionReceipt",
        "∷ ftc2020BannonReplyReceipt",
    ):
        assert marker in ca
    for marker in (
        "ftc2020BannonCourtPetitionOriginalOwner = CA.ftc2020BannonCIDPetitionReceipt",
        "ftc2020BannonOppositionOriginalOwner = CA.ftc2020BannonRespondentOppositionReceipt",
        "ftc2020BannonJudicialShowCauseOriginalOwner = CA.ftc2020BannonJudicialShowCauseReceipt",
        "ftc2020BannonReplyOriginalOwner = CA.ftc2020BannonReplyReceipt",
        "canonicalBannonFTCCIDAdversarialBoundary =",
        "bannon-ftc-cid-adversarial-boundary",
        "ftcBannonDirectAgencyInvestigationSourcePaid = refl",
        "ftcReplyIsNotIndependentNewAgencyProducer = refl",
        "bannonContraryOriginalPleadingRetained = refl",
        "ftcBannonActualCourtSchedulingOrderPaid = refl",
        "ftcBannonCivilCIDIsNotAdjudicatedGuilt = refl",
        "bannonResponseNotJudicialExoneration = refl",
        "ftcBannonCaseOutcomeStillUnverified = refl",
        "ftcBannonCIDDoesNotPayEpsteinMediaTransfer = refl",
        "ftcBannonCIDDoesNotPayWholeNetworkH3 = refl",
    ):
        assert marker in case


def test_ftc_bannon_adversarial_original_docs_not_two_independent_findings():
    report = (ROOT / "docs/research/aquino-epstein-canonical-disposition-20261025.md").read_text()
    for marker in (
        "FTC v Stephen K. Bannon",
        "2020-11-09 petition",
        "Judge Christopher R. Cooper",
        "2020-12-09 opposition",
        "2020-12-18 reply",
        "denies",
        "not a judicial holding",
        "Same FTC producer",
        "not an administrative FTC finding against Bannon",
        "2019 Bannon–Epstein film",
        "H2/H3 remains unestablished",
    ):
        assert marker.lower() in report.lower()


def test_ftc_bannon_cid_conflicting_original_issue_dates_are_not_silently_reconciled():
    case = OWNER.read_text()
    report = (ROOT / "docs/research/aquino-epstein-canonical-disposition-20261025.md").read_text()
    for marker in (
        "federalPetitionSaysCIDIssuedSeptember25 : Bool",
        "signedCourtOrderSaysCIDIssuedSeptember24 : Bool",
        "exactOriginalCIDIssueDateReconciledWithNativeCID : Bool",
        "petitionAnnexExhibit2CIDIndexedAtSeptember24 : Bool",
        "ftcBannonCIDOriginalExhibitLocated = refl",
        "ftcBannonOriginalDateDiscrepancyRecorded = refl",
        "ftcBannonJudicialDateDiscrepancyRecorded = refl",
        "ftcBannonCIDOriginalIssueDateUnpaid = refl",
    ):
        assert marker in case
    for marker in ("September 25, 2019", "September 24, 2019", "not two proven CIDs", "The same November 9 FTC petition", "better supported", "Exhibit 2"):
        assert marker in report


def test_two_original_federal_operations_share_name_not_case_identity():
    bank = (ROOT / "DASHI/Cognition/EpsteinBankingInfrastructureAcquisitionExact.agda").read_text()
    case = OWNER.read_text()
    report = (ROOT / "docs/research/aquino-epstein-canonical-disposition-20261025.md").read_text()
    for fragment in (
        "record ChainReactionFederalNameCollisionCut : Set where",
        "hsiIPR2019FactSheetOriginalInspected : Bool",
        "hsiIPR2019FactSheetSaysStartedJune2011 : Bool",
        "hsiTargetIsCounterfeitGovernmentSupplyChain : Bool",
        "house2022IsSecondIndependentHSIInvestigator : Bool",
        "dea2015MemoCaseNYNYS0829Located : Bool",
        "sameNameMeansSameInvestigation : Bool",
        "agencyOverlapMeansSharedCaseIdentity : Bool",
        "hsiCounterfeitCasesAreDEADrugOffenceDispositions : Bool",
        "reportedJune2023DEAClosureHasSignedNativeInstrumentHere : Bool",
        "canonicalChainReactionFederalNameCollisionCut =",
        "sameOperationNameDoesNotPayCaseIdentity = refl",
        "participatingFederalAgenciesDoNotPayCommonTasking = refl",
        "hsiCounterfeitCasesDoNotDisposeDEAInquiry = refl",
        "secondaryClosureDateNotNativeSignedDEADisposition = refl",
        "hsiChainReaction2019NativeLocator : String",
        "hsiChainReactionCongressionalCarrier : String",
        "hsiChainReaction2011ContemporaneousSenateCarrier : String",
        "hsiChainReaction2011FirstPersonAttribution : String",
        "native page-image receipt is not certified",
        "deaChainReactionDistinctCaseLocator : String",
    ):
        assert fragment in bank
    for fragment in (
        "canonicalFederalChainReactionHomonymOwner =",
        "Banking.canonicalChainReactionFederalNameCollisionCut",
        "chainReactionOriginalNameCollisionNotOneOperation = refl",
        "hsiCounterfeitProceedingsNotEpsteinDrugDisposition = refl",
        "reported2023DEAClosureStillNeedsOriginalInstrument = refl",
    ):
        assert fragment in case
    for fragment in (
        "original 1-page fact sheet",
        "counterfeit microelectronics",
        "16 participating agencies",
        "CHRG-117hhrg50981",
        "Erik Barnett",
        "S.HRG.112-922",
        "screenshot request **timed out**",
        "NY-NYS-0829 / C1-11-0049",
        "16 June 2023",
        "not an independent second HSI investigation",
        "not personally authenticated",
        "high-confidence false-positive removal",
    ):
        assert fragment.lower() in report.lower()


def test_federal_homonym_record_positions_are_fail_closed():
    import re
    bank = (ROOT / "DASHI/Cognition/EpsteinBankingInfrastructureAcquisitionExact.agda").read_text()
    start = bank.index("record ChainReactionFederalNameCollisionCut : Set where")
    end = bank.index("open ChainReactionFederalNameCollisionCut public", start)
    names = re.findall(r"^    ([A-Za-z0-9_]+) : Bool$", bank[start:end], re.M)
    assert len(names) == 14
    start = bank.index("canonicalChainReactionFederalNameCollisionCut =", end)
    end = bank.index("\n\n", start)
    values = re.findall(r"\b(?:true|false)\b", bank[start:end])
    assert len(values) == len(names)
    observed = dict(zip(names, values))
    assert observed["hsiIPR2019FactSheetOriginalInspected"] == "true"
    assert observed["house2022IsSecondIndependentHSIInvestigator"] == "false"
    assert observed["sameNameMeansSameInvestigation"] == "false"
    assert observed["agencyOverlapMeansSharedCaseIdentity"] == "false"
    assert observed["reportedJune2023DEAClosureHasSignedNativeInstrumentHere"] == "false"
    assert observed["sourceProvesEitherCoverupOrSameEpsteinBankTransfer"] == "false"


def test_fec_mur7351_closed_is_not_ftc_bannon_cid_disposition():
    """Separate actual FEC closure from unsighted original FTC judicial order."""
    s = (ROOT / "DASHI/Cognition/BannonCambridgeAnalyticaInfluenceInfrastructureExact.agda").read_text()
    for token in (
        "fecMUR7351OriginalClosureReceipt = bannon-ca-legal-receipt",
        "https://www.fec.gov/data/legal/matter-under-review/7351/",
        "Dismissed-Other",
        "ftcBannonDocketOriginalPublicIndexReceipt = bannon-ca-legal-receipt",
        "1:20-mc-00111-CRC",
        "paglieryJan2021CourtRulingReporting = bannon-ca-legal-receipt",
        "fecClosureCannotCloseFTCBannonCID ()",
        "ftcCACorporateOrderIsNotBannonCIDDisposition ()",
        "NOT signed court-order authentication",
    ):
        # Case-independent source role and historical-status guard.
        if token == "NOT signed court-order authentication":
            assert token in s
        else:
            assert token in s
    assert "true false false" in s
    assert "original signed Jan 2021" not in s.lower() or "NOT inspected" in s
