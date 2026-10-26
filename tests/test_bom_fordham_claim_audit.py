"""Static source-boundary regression for 2026-10 BOM/Fordham case.

This guards source/claim classifications, not climate-data computations, speaker
intent, the original Berger/Sherrington audit, or Agda kernel typechecking.
"""
from pathlib import Path
import csv
from collections import Counter

ROOT = Path(__file__).resolve().parents[1]
OWNER = ROOT / "DASHI/Governance/BOMFordhamMediaClaimAuditExact.agda"
VALIDATION = ROOT / "DASHI/Governance/BOMFordhamMediaClaimAuditValidation.agda"
RESEARCH = ROOT / "docs/bom_fordham_temperature_claim_audit_20261024.md"


def test_existing_typed_genealogy_reused():
    text = OWNER.read_text()
    assert "import DASHI.Governance.TypedGenealogyEdgeExact as Typed" in text
    for edge, kind in [
        ("fordhamTo2GB", "Typed.personnelContinuity"),
        ("radioToTapt", "Typed.organisationalContinuity"),
        ("fordhamAuditBroadcast", "Typed.audienceAdjacency"),
    ]:
        assert edge in text and kind in text
    # No candidate is installed as a strong transfer evidence edge.
    assert "Typed.historicalTransfer Typed.primary" not in text
    assert "Typed.directMethodTransfer Typed.primary" not in text


def test_source_roots_preserve_chronology_and_not_obtained_audit():
    text = OWNER.read_text()
    assert "2026-10-19 AEST" in text
    assert "2026-10-22" in text
    assert "2026-05-01" in text
    assert "canonicalOriginalAuditStatus = notAcquired" in text
    assert "institutionHypothesised bomStatement" in text
    assert "allegationNotReproduced auditReporting" in text


def test_nonpromotion_regressions_and_bondi_distinction():
    code = OWNER.read_text()
    val = VALIDATION.read_text()
    docs = RESEARCH.read_text()
    required = [
        "duplicateDoesNotProveFraud",
        "rhetoricDoesNotProveBannonControl",
        "ownershipDoesNotProveEditorialOrder",
        "bondiCoverageDoesNotProveInflammatorySpeech",
        "fordhamTPUSA", "fordhamTPAU", "fordhamBannon",
    ]
    for name in required:
        assert name in code
    assert "noFraudPromotion" in val
    assert "noTPUSAPromotion" in val
    assert "2024 Bondi Junction" in docs
    assert "2025 Bondi Beach" in docs
    assert "1867 is pre-1910" in docs
    assert "postdates the episode" in docs


def test_bondi_media_and_false_hanson_attribution_are_separate_roots():
    owner = OWNER.read_text()
    docs = RESEARCH.read_text()
    for name in [
        "bondiFordhamPoliticalSegment",
        "fordhamLathamArchive",
        "aapBondiHansonFabrication",
        "tpaustFirstParty",
    ]:
        assert name in owner
    assert "fabricated quotes attributed to Pauline Hanson" in docs
    assert "not anti-Muslim words" in docs
    assert "Latham" in docs and "underlying allegation" not in owner


POLITICAL_OWNER = ROOT / "DASHI/Governance/AustralianPoliticalRadioInfluence2026Exact.agda"
POLITICAL_VALIDATION = ROOT / "DASHI/Governance/AustralianPoliticalRadioInfluence2026Validation.agda"


def test_direct_2026_ownership_and_revenue_do_not_collapse():
    body = POLITICAL_OWNER.read_text()
    docs = RESEARCH.read_text()
    for required in (
        "fordhamTapt",
        "kiisARN",
        "arnSandilandsRevenue",
        "arnNewsCorpExit",
        "19.9 percent",
        "ACMA records News Corp ceased",
        "2026-05-01",
    ):
        assert required in body or required in docs
    assert "noRevenueControlLeap" in body


def test_first_person_messaging_and_disputed_work_status():
    body = POLITICAL_OWNER.read_text()
    val = POLITICAL_VALIDATION.read_text()
    assert "kyleHansonMessaging" in body
    assert "namedActorSelfReport" in body
    assert "ashbyKyleQualification" in body
    assert "namedActorDenial" in body
    assert "noPaidCampaignPromotion" in val


def test_funding_event_attendance_and_climate_are_typed_distinct():
    body = POLITICAL_OWNER.read_text()
    for term in (
        "hancockAdvance",
        "advanceBannonAssociate",
        "harnwellBannon",
        "rinehartHansonPolicy",
        "plimerOneNation",
        "bannonPalmerCanonicalOwner",
        "acmaMpoxFinding",
        "acmaParalympicsFinding",
        "noFordhamCommandLeap",
    ):
        assert term in body
    assert "EFTA01615861" in body
    assert "palmerBannonConflict = relationship-receipt" not in body
    assert "noConferenceCommand" in POLITICAL_VALIDATION.read_text()


FRIENDLY = ROOT / "DASHI/Governance/FriendlyjordiesABCFazalSourceAudit2026Exact.agda"
FRIENDLY_CHECKS = ROOT / "DASHI/Governance/FriendlyjordiesABCFazalSourceAudit2026Validation.agda"


def test_single_owner_for_bannon_palmer_and_source_root():
    body = POLITICAL_OWNER.read_text()
    assert 'BannonFaragePalmerAutomatedInfluenceReceiptsExact' in body
    assert 'EFTA01615861' in body
    assert "palmerBannonConflict = relationship-receipt" not in body
    assert "bannonPalmerCanonicalOwner" in body


def test_new_show_legal_operator_and_investor_state():
    body = POLITICAL_OWNER.read_text()
    for token in (
        "newShowLegalOperator",
        "sandilandsSelfReportedOwnership",
        "aiimsProduction",
        "nineTaptStrategicPartnership",
        "kyleProposedARNBuyout",
        "Kyle Sandilands Live Pty Ltd",
        "ABN 24 699 610 261",
        "NET revenue",
        "thresholds/caps",
    ):
        assert token in body


def test_recent_friendlyjordies_independent_abc_findings():
    body = FRIENDLY.read_text()
    checks = FRIENDLY_CHECKS.read_text()
    for token in (
        "friendlyjordiesGovernanceWitness",
        "SensibLawFriendlyjordiesSourceTotalityExact",
        "breaking my silence",
        "2026-10-22",
        "2026-10-23",
        "Cocaine Nation",
        "Meth Highway",
        "abcOmbudsmansDetermination",
        "lamestreamCountercheck",
        "reportedWithDenial",
        "shanksHomeArsonNov2022",
        "bondiJunctionAttackApr2024",
        "bondiBeachAttackDec2025",
    ):
        assert token in body
    assert "editorialFailureNotCriminalThreat" in checks
    assert "screenshotProvenanceRequired" in checks


def test_arn_presenter_contractors_are_historical_equity_not_ksl_investors():
    body = POLITICAL_OWNER.read_text()
    vals = POLITICAL_VALIDATION.read_text()
    research = RESEARCH.read_text()
    for token in (
        "quasarARNHistoricalEquity",
        "hendersonARNHistoricalEquity",
        "quasarKyleService",
        "southernCrossARNIndirect",
        "stokesSouthernCrossStake",
        "3,161,166",
        "historicEquityHolding",
    ):
        assert token in body or token in research
    assert "newShowOperatorIsNotOwnership" in vals
    assert "proposedBuyoutIsNotCompleted" in vals
    assert "quasarServiceIsNotNewShowEquity" in vals
    assert "ACMA says News Corp Australia" in research


def test_direct_original_abc_ombudsman_five_findings_and_seven_actions():
    source = FRIENDLY.read_text()
    proofs = FRIENDLY_CHECKS.read_text()
    for token in (
        "ombudsmanOriginalExecutiveSummary",
        "39e8eeeffed7acde9a54d3ccc2f2a6fb",
        "finding1DoublePresentation",
        "finding2JasonVerification",
        "finding3SweeperApproval",
        "finding4BrendanContext",
        "finding5InstitutionalIntegrity",
        "canonicalFiveOmbudsmanFindings",
        "r1RemoveProgrammes",
        "r2BroaderInquiry",
        "r3PublishCorrection",
        "r4NamedAnonymityApprover",
        "r5LegalVersusEditorialRisk",
        "r6FactcheckAndUpwardReferral",
        "r7JuniorTeamSupport",
        "canonicalSevenOmbudsmanRecommendations",
        "institutionalAcceptanceDoesNotPayCompletion",
    ):
        assert token in source
    assert "acceptanceDoesNotVerifyCompletion" in proofs
    assert "findingFiveIsInstitutionalIntegrity" in proofs


def test_no_invented_ai_mode_claims_or_external_investors():
    documentation = RESEARCH.read_text()
    media = POLITICAL_OWNER.read_text()
    checks = POLITICAL_VALIDATION.read_text()
    assert "https://share.google/aimode/Ux4UtsL535FOH9STw" in documentation
    # The original October 24 acquisition failure is now superseded by
    # the user-supplied transcript; its generated claims are not evidence.
    assert "SUPERSEDED by 25 October uploaded transcript" in documentation
    assert "Google AI Mode transcript acquired" in documentation
    assert "80b27d5b866a0a906142a6c66f3e090ad39342ecbe4173f088ef48ea61adbfcc" in documentation
    for receipt in (
        "kyleSubscriberFinanceSelfReport",
        "harveyNormanProspectiveSponsorship",
        "kyleUscreenPlatform",
    ):
        assert receipt in media
    assert "reportedSubscriptionsNotAudited" in media
    assert "advertiserOfferNotEquity" in media
    assert "subscriberFundingIsAttributedOnly" in checks
    assert "advertiserInterestNotCapitalStake" in checks


def test_google_ai_source_intake_reuses_political_radio_owner():
    """No source-specific Agda files for one AI-generated answer."""
    governance = ROOT / "DASHI/Governance"
    for obsolete in (
        "GoogleAIModeMediaClaimIntake2026Exact.agda",
        "GoogleAIModeMediaClaimIntake2026Validation.agda",
    ):
        assert not (governance / obsolete).exists()

    source = POLITICAL_OWNER.read_text()
    checks = POLITICAL_VALIDATION.read_text()
    docs = RESEARCH.read_text()
    # Every retained relationship has a direct, source-graded owner here;
    # other speculative leads stay only in the narrative evidence ledger.
    for receipt in (
        "rinehartBannonDevineEvent",
        "advanceSheahanBannonConversation",
        "rinehartMcWilliamSecuredMediaStake",
        "rinehartStefanovicPodcastFundingClaim",
        "stefanovicRobinsonPublication",
        "hansonRepublishedRobinson",
        "mandelsonXstrataEpsteinTaxEmail",
        "jonesGillardRecordedRemark",
        "rinehartOneNationHeadOffice",
        "stefanovicIbrahimOwnershipSettlement",
        "mfwKyleAdvertiserCampaign",
    ):
        assert source.count(receipt + " : RelationshipReceipt") == 1

    for proof in (
        "rinehartStakeIsSecuredFinancing",
        "stefanovicFundingRemainsReported",
        "hansonRepostIsRedistribution",
        "sheahanChatRemainsReported",
        "taxEvidenceIsCorrespondence",
        "headquartersIsReportedLease",
        "podcastBuyoutNotRinehartEquity",
        "MFWPressureIsAdvertiserCampaign",
    ):
        assert proof in checks

    assert "PR #1131" in docs
    assert "not its own mathematical owner" in docs
    assert "DASHI.Governance.GoogleAIModeMediaClaimIntake2026" not in source + checks


def test_cross_pollination_reuses_woogaroo_climate_and_project2025_owners():
    """A bounded effect question isn't a new claim of gas lobbying or US direction."""
    political = POLITICAL_OWNER.read_text()
    docs = RESEARCH.read_text()
    for token in (
        "independentOriginalClaimConcentration",
        "donorAdjacentGasPolicyShift",
        "project2025PolicyProposalVersusEnactment",
        "springfieldResidentialGasDemandPersistence",
    ):
        assert token in political

    for source_owner in (
        "SensibLawSpringfieldGasLobbyingOwnershipSnowballExact",
        "SensibLawAzureSpringfieldInducedGasDemandExact",
        "HansonCapacityCriticismHyperformalismExact",
        "ClimateGenealogyTypedCasesExact",
        "GodsEyeViewWorldEpistemicSourceAtlasExact",
        "GodsEyeViewDiagnosisDrivenActivistRollupExact",
    ):
        assert source_owner in docs

    for bounded_claim in (
        "10.1177/09636625231202117",
        "10.1038/s41598-021-01714-4",
        "8,000 gas connections",
        "Bernard L. McNamee",
        "Mandy M. Gunasekara",
        "same-object",
        "N_eff",
        "Senex 8 May 2026",
        "One Nation 9 June 2026",
    ):
        assert bounded_claim in docs

    # No duplicated named company/donation source receipts are placed into
    # the media file, and no unsupported lobbying→appliance causal edge exists.
    assert "azureLnpDonation2019A = attributed-influence-edge" not in political
    assert "springfieldRegisteredLobbyistMeeting2025 = attributed-influence-edge" not in political
    assert "actual same-object policy-to-asset-to-household" not in political


ORIGIN_EDGE_LEDGER = ROOT / "Docs/support/reference/australian_climate_claim_origin_edges_20261025.csv"


def test_original_claim_edges_are_source_qualified_and_do_not_invent_transfers():
    """Machine-check source families, chronology and non-causality boundaries."""
    with ORIGIN_EDGE_LEDGER.open(newline="", encoding="utf-8") as stream:
        rows = list(csv.DictReader(stream))

    assert len(rows) == 54
    assert len({row["edge_id"] for row in rows}) == len(rows)
    assert Counter(row["case_id"] for row in rows) == {
        "BOM2026": 24, "REEF2021": 10, "GAS2026": 20
    }
    fields = (
        "edge_id", "case_id", "upstream", "downstream", "relation",
        "evidence_grade", "date_local_or_month", "locator", "boundary"
    )
    assert all(all(row.get(field) for field in fields) for row in rows)
    assert all(row["locator"].startswith("https://") for row in rows)
    assert all(len(row["boundary"]) >= 40 for row in rows)

    # Reported interpretations are not the original science.
    reef_opinion = next(row for row in rows if row["edge_id"] == "R03")
    assert reef_opinion["relation"] == "named_alternative_interpretation"
    assert "not AIMS conclusion" in reef_opinion["boundary"]

    # An FOI-supported leak is real while Ridd's opinion commission is not proven.
    selected_media = next(row for row in rows if row["edge_id"] == "R02")
    assert selected_media["evidence_grade"] == "foi_reported_by_abc"
    assert "distinct from Ridd" in selected_media["boundary"]

    # ACMA specific 2023 determinations do not adjudicate entire Sky network.
    acma = next(row for row in rows if row["edge_id"] == "R07")
    assert acma["evidence_grade"] == "acma_determination"
    assert "not all Sky" in acma["boundary"]

    # The May primary policy statement precedes the June party policy. Their
    # similarity is not documentary proof of transmission or a payment.
    gas = next(row for row in rows if row["edge_id"] == "G01")
    assert gas["relation"] == "argument_overlap_not_copy_proof"
    assert gas["evidence_grade"] == "two_independent_primary_texts"
    assert "2026-05-08/2026-06-09" in gas["date_local_or_month"]
    assert "no proved" in gas["boundary"]

    # Claims of provenance are not evidence just because many republications
    # share the same origin; explicitly mark secondary byline propagation.
    publications = [
        row for row in rows if row["relation"] in {
            "credited_guest_publication",
            "explicit_author_republication",
            "explicitly_credited_reporting",
            "credited_crosspublication",
        }
    ]
    assert len(publications) >= 5
    assert all(
        row["evidence_grade"] in {
            "same_author_content", "named_original_reporter"
        } for row in publications
    )


def test_claim_root_ledger_documentation_uses_only_case_bounded_counts():
    docs = RESEARCH.read_text()
    assert "australian_climate_claim_origin_edges_20261025.csv" in docs
    assert "54 bounded relationship rows" in docs
    assert "NOT a representative crawl" in docs
    assert "originator" in docs.lower()
    assert "actual transfer not established" in docs.lower()


def test_directed_release_and_original_claim_amplification_are_not_collapsed():
    media = POLITICAL_OWNER.read_text()
    checks = POLITICAL_VALIDATION.read_text()
    for original, kind in (
        ("leyAimsTargetedMediaPreview", "timedTargetedInformationRelease"),
        ("riddIndependentReefOpinion", "originalOpinionProduction"),
        ("mooreAmplifiedRiddReefClaim", "traceableClaimAmplification"),
        ("acmaReefOutsidersFinding", "enforcementFinding"),
    ):
        assert media.count(original + " : RelationshipReceipt") == 1
        assert kind in media

    for token in (
        "reefReleaseIsTimedMediaAccess",
        "riddOpinionNotAimsMeasurement",
        "mooreRepostNotIndependentMeasurement",
        "reefRegulatoryFindingIsSpecific",
        "reefReleaseNotMinistryEditorialControl",
        "riddDistributionNotCoordinatedCommand",
    ):
        assert token in checks
    assert "BI-645, BI-646, BI-647" in media
    assert "not proof" in media.lower()


def test_original_bom_clips_and_historical_ipa_finance_use_different_types():
    with ORIGIN_EDGE_LEDGER.open(newline="", encoding="utf-8") as stream:
        by_id = {row["edge_id"]: row for row in csv.DictReader(stream)}

    assert by_id["B10"]["relation"] == "direct_clip_reuse_in_transcript"
    assert by_id["B11"]["relation"] == "hosted_interview_republication"
    assert by_id["B10"]["downstream"].startswith("Sky News Outsiders")
    assert by_id["R09"]["evidence_grade"] == "ipa_first_party_press_release"
    assert by_id["R10"]["relation"] == "historical_institutional_donation"
    assert "not payment to Ridd or Sky" in by_id["R10"]["boundary"]

    docs = RESEARCH.read_text()
    assert "Peter Ridd on Outsiders News24" in docs
    assert "Hancock Prospecting" in docs
    assert "no same-object payment" in docs
    assert "Fordham's production" in docs


def test_single_bom_sky_clip_ipa_publication_and_old_donor_not_collapsed():
    media = POLITICAL_OWNER.read_text()
    validation = POLITICAL_VALIDATION.read_text()
    for name in (
        "skyOutsidersLloydRiddSameProgramme",
        "ipaHostsBOMOutsidersTranscript",
        "ipaRiddResearchFellowship",
        "hancockToIPAHistoricalFunding",
    ):
        assert media.count(name + " : RelationshipReceipt") == 1

    for name in (
        "outsidersLloydRiddSameProgrammeIsPublished",
        "ipaOwnTranscriptIsDerivativePublication",
        "riddFellowshipIsNamedInstitutionalRelation",
        "historicHancockIPAIsNotCurrentEarmarkedPayment",
        "historicalIPAReceiptNotEditorialOrder",
        "publishedBOMInterviewNotSecretCommand",
    ):
        assert name in validation

    assert "historicalInstitutionalFunding" in media
    assert "4.5m" in media
    assert "no same-object payment" in RESEARCH.read_text()


def test_international_republication_is_not_fresh_climate_evidence():
    with ORIGIN_EDGE_LEDGER.open(newline="", encoding="utf-8") as stream:
        entries = {r["edge_id"]: r for r in csv.DictReader(stream)}
    assert entries["B12"]["relation"] == "explicit_international_translation"
    assert entries["B12"]["evidence_grade"] == "first_party_translation_credit"
    assert entries["B13"]["relation"] == "news_digest_reference"
    assert entries["B13"]["evidence_grade"] == "named_source_linking"
    assert "No independent BOM ledger verification" in entries["B12"]["boundary"]
    assert "not independent audits" in RESEARCH.read_text()


def test_canonical_origin_keys_do_not_miscount_common_republication():
    with ORIGIN_EDGE_LEDGER.open(newline="", encoding="utf-8") as stream:
        rows = list(csv.DictReader(stream))
    assert len(rows) == 54
    assert all(row["root_key"] and row["root_resolution"] for row in rows)
    by_id = {row["edge_id"]: row for row in rows}
    assert by_id["G05"]["root_key"] == by_id["G06"]["root_key"] == "G_CREIGHTON_OPINION"
    assert by_id["G07"]["root_key"] == by_id["G08"]["root_key"] == "G_JOHNSON_REPORT"
    assert by_id["B03"]["root_key"] == by_id["B12"]["root_key"] == "B_NOVA_COMMENTARY"
    assert by_id["G01"]["root_key"] == "MULTI"
    assert by_id["G09"]["root_key"] == "MULTI"
    assert by_id["G10"]["root_key"] == "MULTI"
    assert by_id["G13"]["root_key"] == "MULTI"
    # The 31 source/template family labels are manually assigned within this purposive case
    # graph, not a statistic of Australian media or distinct truth sources.
    labeled = {r["root_key"] for r in rows if r["root_key"] != "MULTI"}
    assert len(labeled) == 31
    assert sum(r["root_key"] == "MULTI" for r in rows) == 9


def test_senex_hancock_ipa_information_path_has_explicit_public_countercase():
    media = POLITICAL_OWNER.read_text()
    proofs = POLITICAL_VALIDATION.read_text()
    doc = RESEARCH.read_text()
    for receipt in (
        "creightonIPAOriginalArticle",
        "senexLinksIPACreighton",
        "hancockReprintsJohnsonNightly",
        "senexLinksJohnsonNightly",
        "senateGasTaxInquiryPublicComparator",
    ):
        assert media.count(receipt + " : RelationshipReceipt") == 1
    for witness in (
        "creightonOriginalCreditIsAttributedReuse",
        "gasProducerLinksIPAOriginal",
        "hancockSameJournalismNotIndependentData",
        "senexSameJournalismNotIndependentData",
        "parliamentaryPublicPolicyCounterexample",
        "gasRepublishingDoesNotEstablishPolicyCopy",
        "politicalLanguageDoesNotEstablishCommonSponsor",
    ):
        assert witness in proofs
    assert "No new Agda ontology" in doc
    assert "Stephen Johnson" in doc and "Adam Creighton" in doc
    assert "230+ submissions" in doc
    assert "31 selected source/template family labels" in doc


def test_one_nation_gas_policy_is_not_dated_before_public_inquiry():
    doc = RESEARCH.read_text()
    assert "Senate committee **7 May** report" in doc
    assert "One Nation's **9 June**" in doc
    assert "7 May precedes 8 May" in doc
    assert "actual transfer not established" in doc.lower()


def test_two_independent_political_frames_inside_single_sky_interview():
    media = POLITICAL_OWNER.read_text()
    validation = POLITICAL_VALIDATION.read_text()
    documentation = RESEARCH.read_text()
    with ORIGIN_EDGE_LEDGER.open(newline="", encoding="utf-8") as stream:
        keyed = {r["edge_id"]: r for r in csv.DictReader(stream)}

    assert keyed["B14"]["root_key"] == "B_RIDD_2026_INTERVIEW"
    assert keyed["B15"]["root_key"] == "B_DEAN_2026_SHOW_FRAME"
    assert keyed["B14"]["root_key"] != keyed["B15"]["root_key"]
    assert "not verified" in keyed["B14"]["boundary"]
    for name in ("riddBOMGasLitigationArgument", "rowanDeanBOMNetZeroArgument"):
        assert media.count(name + " : RelationshipReceipt") == 1
    for name in ("riddCrossDomainIsAttributedArgument", "deanClimatePolicyIsAttributedArgument",
                 "riddClaimDoesNotProveGasLitigationCausality", "deanClaimDoesNotProvePoliticalCoordination"):
        assert name in validation
    assert "unspecified Western Australian gas project" in documentation
    assert "31 selected source/template family labels" in documentation


def test_browse_epbc_primary_request_cannot_promote_expert_claim_to_decision():
    media = POLITICAL_OWNER.read_text()
    validation = POLITICAL_VALIDATION.read_text()
    docs = RESEARCH.read_text()
    for named in (
        "browseACFOriginalS78AApplication",
        "browse2026ValidityDecisionOnly",
        "browseCitedAbramScienceMethod",
        "perkinsKirkpatrickBrowseExpertModel",
        "riddSpecificBrowseReferentInference",
        "fordhamOriginalFourMinutePodcastCarrier",
    ):
        assert media.count(named + " : RelationshipReceipt") == 1
    for proof in (
        "browseRequestIsNotCourtJudgment",
        "validityOnlyNotFinalDecision",
        "abramMethodPrecedesSpecificBrowseEstimate",
        "specificExpertModelNotMeasurement",
        "unnamedRiddGasReferentIsInferred",
        "fourMinuteAudioLocatorNotTranscript",
        "epbcProceduralStatusDoesNotProveMerits",
        "fourMinutePodcastLocatorDoesNotProveWords",
        "similarNumDoesNotProveSourceConsulted",
    ):
        assert proof in validation
    assert "2018/8319" in media and docs
    assert "29.35" in media and docs
    assert "10.1038/s44168-025-00296-5" in media and docs
    assert "not a substantive merits decision" in docs.lower()
    assert "Annexure A" in media


def test_fordham_publication_time_and_browse_original_root_split():
    import datetime
    from zoneinfo import ZoneInfo

    with ORIGIN_EDGE_LEDGER.open(newline="", encoding="utf-8") as stream:
        items = {row["edge_id"]: row for row in csv.DictReader(stream)}
    assert len(items) == 54
    assert items["B16"]["root_key"] == "MULTI"
    assert items["B21"]["root_key"] == "MULTI"
    assert items["G14"]["root_key"] == "MULTI"
    assert items["B17"]["root_key"] == "B_ACF_BROWSE_REQUEST"
    assert items["B18"]["root_key"] == "B_ABRAM_2025_METHOD"
    assert items["B19"]["root_key"] == "B_PERKINS_BROWSE_EXPERT"
    assert items["B20"]["root_key"] == "B_FORDHAM_AUDIO"
    assert items["B20"]["root_resolution"] == "native_publication_identity_no_spoken_quote"

    utc = datetime.datetime(2026, 10, 18, 21, 55, tzinfo=datetime.timezone.utc)
    brisbane = utc.astimezone(ZoneInfo("Australia/Brisbane"))
    assert (brisbane.year, brisbane.month, brisbane.day, brisbane.hour, brisbane.minute) == (2026, 10, 19, 7, 55)

    docs = RESEARCH.read_text()
    assert "54 evidence edges" in docs  # current sample after acquisition
    assert "not a court lawsuit" in docs
    assert "not a court lawsuit" in docs and "not a substantive merits decision" in docs.lower()


def test_gas_committee_five_form_letters_are_template_counts_not_five_authors():
    with ORIGIN_EDGE_LEDGER.open(newline="", encoding="utf-8") as stream:
        rows = {row["edge_id"]: row for row in csv.DictReader(stream)}
    templates = {"G15":272, "G16":13, "G17":52, "G18":15, "G19":14}
    assert sum(templates.values()) == 366
    for ref, count in templates.items():
        row = rows[ref]
        assert row["relation"] == "documented_form_letter_template_repeat"
        assert row["evidence_grade"] == "senate_committee_primary_report_paragraph_1_6"
        assert str(count) in row["downstream"]
        assert row["root_key"].startswith("G_TEMPLATE_")
    # Three template creators are explicitly unknown; a technology platform
    # is not established as the author of the campaign text it transmitted.
    for ref in ("G15", "G18", "G19"):
        assert rows[ref]["root_resolution"] == "committee_template_identity_author_unknown"
    assert rows["G17"]["root_resolution"] == "platform_route_not_original_text_author"
    assert rows["G20"]["root_key"] == "G_GETUP_PETITION"
    assert "50000" in rows["G20"]["downstream"]
    assert "not 50000 independent" in rows["G20"]["boundary"]

    media = POLITICAL_OWNER.read_text()
    validation = POLITICAL_VALIDATION.read_text()
    for name in ("gasTaxSenateFiveTemplateFamilies", "gasTaxGetUpPetitionAggregate"):
        assert media.count(name + " : RelationshipReceipt") == 1
    for proof in (
        "gasTemplateFamiliesAreDistinctFromIndependentModels",
        "getupPetitionCountsSupportNotIndependentModels",
        "noConspiracyFromTemplateCounts",
    ):
        assert proof in validation


def test_bom_report_custody_is_not_access_to_original_audit():
    with ORIGIN_EDGE_LEDGER.open(newline="", encoding="utf-8") as stream:
        item = {r["edge_id"]:r for r in csv.DictReader(stream)}["B22"]
    assert item["root_key"] == "B_AUDIT_ATR"
    assert item["relation"] == "reported_private_copy_and_permission_constraint"
    assert "not released or inspected" in item["boundary"]
    media = POLITICAL_OWNER.read_text()
    validation = POLITICAL_VALIDATION.read_text()
    assert media.count("novaClaimsFullBOMAuditCopy : RelationshipReceipt") == 1
    assert "unpublishedAuditPossessionNotSourceInspection" in validation
    assert "noProvenAuditFromPersonalCustodyReport" in validation


def test_browse_central_estimate_exact_rational_consistency_only():
    """Checks conditional arithmetic, NOT ecological validity or uncertainty."""
    from fractions import Fraction as Q
    browse_emissions_mt = Q("1597.41")
    tcre_c_per_million_mt = Q("0.45") / 1_000_000
    gbr_dhw_per_c = Q("4.4")
    cover_fraction_per_dhw = Q("0.035")
    hectares = 1_060_000
    colonies_per_hectare = 250_000

    warming = browse_emissions_mt * tcre_c_per_million_mt
    dhw = warming * gbr_dhw_per_c
    cover_loss_fraction = dhw * cover_fraction_per_dhw
    estimated_colonies = cover_loss_fraction * hectares * colonies_per_hectare
    assert warming == Q(1437669, 2000000000)
    assert estimated_colonies == Q(5867127189, 200)  # 29,335,635.945
    assert abs(estimated_colonies - 29_350_000) / 29_350_000 < Q(1, 2000)

    # The paper's independently described Scarborough example (~16m)
    # uses the same method but a *different project emissions input*.
    scarborough = Q(876) * tcre_c_per_million_mt * gbr_dhw_per_c * cover_fraction_per_dhw * hectares * colonies_per_hectare
    assert scarborough == 16_087_302

    docs = RESEARCH.read_text()
    assert "29,335,635.945" in docs
    assert "16,087,302" in docs
    assert "kernel-verified Agda theorem" in docs


def test_finite_agda_template_and_browse_arithmetic_witnesses_declared():
    """Declaration and source checks only; this is NOT a kernel typecheck."""
    proofs = POLITICAL_VALIDATION.read_text()
    assert "open import Agda.Builtin.Nat using (_+_; _*_)" in proofs
    assert "gasCommitteeOriginalTemplateTotals" in proofs
    assert "272 + 13 + 52 + 15 + 14 ≡ 366" in proofs
    assert "browseConditionalModelNumeratorExact" in proofs
    assert "159741 * 45 * 44 * 35 * 1060000 * 250000" in proofs
    assert "2933563594500000000000" in proofs
    assert "browseConditionalModelScaleExact" in proofs
    assert "5867127189 * 500000000000" in proofs
    assert "does not make them" in proofs


def test_readfearn_precision_countercheck_and_annex_index_are_distinct_sources():
    """An independent news analysis is not an instrument log; an index is not a PDF."""
    with ORIGIN_EDGE_LEDGER.open(newline="", encoding="utf-8") as stream:
        entries = {r["edge_id"]: r for r in csv.DictReader(stream)}
    assert entries["B23"]["root_key"] == "B_READFEARN_METHOD_CHECK"
    assert entries["B23"]["relation"] == "journalistic_adversarial_primary_method_query"
    assert entries["B23"]["evidence_grade"] == "named_journalist_original_report"
    assert "not independent 2004 temperature measurement" in entries["B23"]["boundary"]
    assert entries["B24"]["root_key"] == "B_PERKINS_BROWSE_EXPERT"
    assert entries["B24"]["root_resolution"] == "original_pdf_listed_retrieval_unpaid"
    assert "uninspected" in entries["B24"]["boundary"]

    original = (ROOT / "DASHI/Governance/BOMFordhamMediaClaimAuditExact.agda").read_text()
    validation = (ROOT / "DASHI/Governance/BOMFordhamMediaClaimAuditValidation.agda").read_text()
    sensitivity = (ROOT / "tests/test_bom_climate_sensitivity_bounds.py").read_text()
    for token in (
        "readfearnPalmervillePrecisionCheck",
        "palmervillePrecisionLossWitness",
        "INF.NonFactorabilityWitness",
        "palmervilleRoundedValuesCannotDetermineUnroundedDayOne",
        "palmervilleDifferentUnderlyingValue",
    ):
        assert token in original
    for token in (
        "palmervilleDistinctHistoriesSameSeventeenRoundedObservations",
        "palmervilleDifferentLatentDayOneIsNotRecoverable",
        "palmervilleMeasurementPrecisionNotAProbability",
        "INF.FactorsThrough",
    ):
        assert token in validation
    assert "test_seventeen_identical_rounded_days_do_not_identify_latent_tenths" in sensitivity
    assert "test_integer_precision_preserves_a_nontrivial_degree_bin" in sensitivity

    docs = RESEARCH.read_text()
    assert "The two constructed histories are illustrative" in docs
    assert "source-content gap" in docs
    assert "706 KB" in docs
    assert "31 manually curated root-or-template labels" in docs


def test_climate_origins_same_api_plan_and_actual_people_not_url_multiplicity():
    """Independent plan authorship and named people are not 13 independent scientific papers."""
    import re
    climate = (ROOT / "DASHI/Governance/ClimateGenealogyTypedCasesExact.agda").read_text()
    validation = (ROOT / "DASHI/Governance/EmpiricalGenealogyRound3Regression.agda").read_text()
    manifest = ROOT / "Docs/support/reference/climate_genealogy_typed_edges.csv"
    with manifest.open(newline="", encoding="utf-8") as src:
        records = list(csv.DictReader(src))
    assert len(records) == 36
    ids = [r["edge_id"] for r in records]
    assert len(ids) == len(set(ids))
    contributed = [r for r in records if re.fullmatch(r"E8-\d\d", r["edge_id"])]
    assert len(contributed) == 13
    assert all(r["evidence_strength"] == "A_primary" for r in contributed)
    assert all("US Congressional Record 27 Apr 1998" in r["source_citation"] for r in contributed)
    assert all("not" in r["notes"].lower() for r in contributed)
    assert len(re.findall(r"^apiNamedContributor\w+ : Typed.TypedGenealogyEdge$", climate, re.MULTILINE)) == 13
    assert "allAPIContributorsInExampleShareOneOriginalDocument" in validation

    by_id = {r["edge_id"]: r for r in records}
    assert by_id["E9-08"]["relation_kind"] == "funding"
    assert by_id["E9-08"]["evidence_strength"] == "A_primary"
    assert by_id["E9-09"]["relation_kind"] == "organizational_continuity"
    assert by_id["E9-10"]["relation_kind"] == "personnel_continuity"
    assert by_id["E9-11"]["relation_kind"] == "personnel_continuity"
    assert "Steve Milloy" in by_id["E9-11"]["from_node"]

    for item in (
        "exxonInternal1982", "shellInternal1988", "gccLennyBernstein1995",
        "shellFirstParty1998", "bpLeadership1997",
        "mooreCO2Coalition", "mooreHeartland", "greenpeaceHistory",
        "hancockIPAJudgment", "brulleFoundationStudy",
        "farrellNetworkStudy", "supranRahmstorfOreskesExxonAudit",
        "milloy1998ToReefMedia",
    ):
        assert item in climate
    for caution in (
        "apiContributorNotMethodTransfer", "ipaFundingNotEditorialMethod",
        "cfactContinuationNotPlanTransfer", "milloyRepeatNotProofOfTwentyThreeYearPlan",
    ):
        assert caution in climate

    docs = RESEARCH.read_text()
    assert "26 October 2026 — funded climate countermovement originators" in docs
    assert "900m amount includes all activities" in docs.lower() or (
        "900m amount includes all activities" in climate.lower()
    ) or "900m amount includes all activities" in docs.lower()
    assert "36 rows" in docs
    assert "same-NAMED-PERSON continuity" in docs


def test_climate_original_claim_proofs_do_not_promote_funding_to_edits():
    climate = (ROOT / "DASHI/Governance/ClimateGenealogyTypedCasesExact.agda").read_text()
    val = (ROOT / "DASHI/Governance/EmpiricalGenealogyRound3Regression.agda").read_text()
    for item in (
        "apiPlanParticipationCannotBecomeMethodTransmission",
        "hancockIPAFundingCannotBecomeAutomaticMessageControl",
        "cfact1998And2026DoNotAutomaticallyProveContinuousPlan",
        "milloy1998To2021IsPersonnelNotScriptTransmission",
        "repeatPersonDoesNotProveOriginalAPIPlanStillActive",
        "foundationIncomeNotSameAsClimateDenialExpenditure",
        "industryDefectionsNotErased",
    ):
        assert item in val
    assert "typedGenealogyEdge" in climate
    assert "false false false" not in climate  # not a new political-radio triple system


def test_original_ice_and_singer_budget_states_do_not_invent_payment():
    typed = (ROOT / "DASHI/Governance/TypedGenealogyEdgeExact.agda").read_text()
    climate = (ROOT / "DASHI/Governance/ClimateGenealogyTypedCasesExact.agda").read_text()
    validation = (ROOT / "DASHI/Governance/EmpiricalGenealogyRound3Regression.agda").read_text()
    with (ROOT / "Docs/support/reference/climate_genealogy_typed_edges.csv").open(
        newline="", encoding="utf-8"
    ) as fd:
        cases = {r["edge_id"]: r for r in csv.DictReader(fd)}
    assert len(cases) == 36
    assert cases["E9-12"]["relation_kind"] == "organizational_continuity"
    assert cases["E9-13"]["relation_kind"] == "funding_commitment"
    assert cases["E9-14"]["relation_kind"] == "organizational_continuity"
    assert cases["E9-15"]["relation_kind"] == "funding_proposal"
    assert cases["E9-13"]["evidence_strength"] == "B_corroborated"
    assert cases["E9-15"]["evidence_strength"] == "A_primary"
    assert "payment transaction not independently inspected" in cases["E9-13"]["notes"]
    assert "not evidence it was disbursed" in cases["E9-15"]["notes"]

    for exact in ("fundingProposal : RelationKind", "fundingCommitment : RelationKind",
                  "fundingProposalIsNotTransferRelation", "fundingCommitmentIsNotTransferRelation"):
        assert exact in typed
    for item in ("ice1991TestCampaign", "singerGCC1994Proposal",
                 "southernCompany1991To1998", "southernICEPledgeNotDisbursement",
                 "singer1994ToSEPP1998", "singerGCCSolicitationNotMoneyPaid"):
        assert item in climate
    for item in ("singerGCCBudgetIsRequestNotPaidGrant",
                 "southernICEBudgetIsCommitmentNotBankTransfer",
                 "singer1994ProposalCannotEstablishMethodTransfer",
                 "southern1991PledgeCannotEstablishMethodTransfer"):
        assert item in validation
    doc = RESEARCH.read_text()
    assert "36 rows total" in doc
    assert "Singer → tobacco funders" in doc
    assert "this audit has **not acquired** a specific dated BP internal technical memo" in doc
