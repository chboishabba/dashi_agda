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
    assert 'original DOJ-native custody and complete surrounding thread were not checked' in source
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
    assert "not direct CA privity" in source
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
        "bannonEpsteinWorkProductCut = case-dependency-cut",
        "April 3 2019 EFTA00809863-Indyke letter located",
        "Film already exists.",
        "source timestamps",
        "preExistingFilmedInterviewIsPaid = refl",
        "caseWholeH2Unpaid = refl",
        "caseCovertH3Unpaid = refl",
    ):
        assert token in source
    assert "not a verified signed/accepted contract" not in source  # forbid fabricated acceptance
